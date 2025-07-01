// Copyright 2024 The XLS Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "xls/passes/select_lifting_pass.h"

#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "absl/log/log.h"
#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "xls/common/status/matchers.h"
#include "xls/common/status/status_macros.h"
#include "xls/ir/bits.h"
#include "xls/ir/function.h"
#include "xls/ir/function_builder.h"
#include "xls/ir/ir_test_base.h"
#include "xls/ir/op.h"
#include "xls/ir/package.h"
#include "xls/passes/dce_pass.h"
#include "xls/passes/optimization_pass.h"
#include "xls/passes/pass_base.h"

namespace xls {

namespace {

class SelectLiftingPassTest : public IrTestBase {
 protected:
  SelectLiftingPassTest() = default;

  absl::StatusOr<bool> Run(Function* f) {
    PassResults results;
    OptimizationContext context;

    // Run the select lifting pass.
    XLS_ASSIGN_OR_RETURN(bool changed,
                         SelectLiftingPass().RunOnFunctionBase(
                             f, OptimizationPassOptions(), &results, context));

    // Run dce to clean things up.
    XLS_RETURN_IF_ERROR(
        DeadCodeEliminationPass()
            .RunOnFunctionBase(f, OptimizationPassOptions(), &results, context)
            .status());

    // Return whether select lifting changed anything.
    return changed;
  }
};

TEST_F(SelectLiftingPassTest, LiftSingleSelect) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);

  // Create the parameters of the IR function
  BValue a = fb.Param("array", p->GetArrayType(16, u32_type));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);
  BValue j = fb.Param("second_index", u32_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i});
  BValue array_index_j = fb.ArrayIndex(a, {j});
  BValue select_node = fb.Select(selector, array_index_i, array_index_j);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  VLOG(3) << "Before the transformations: " << f->DumpIr();
  EXPECT_EQ(f->node_count(), 9);
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(true));
  VLOG(3) << "After the transformations:" << f->DumpIr();
  EXPECT_EQ(f->node_count(), 8);
  VLOG(3) << f->DumpIr();
}

TEST_F(SelectLiftingPassTest, LiftSingleSelectNotModifiedDueToDifferentInputs) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);

  // Create the parameters of the IR function
  BValue a = fb.Param("array", p->GetArrayType(16, u32_type));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);
  BValue j = fb.Param("second_index", u32_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i});
  BValue select_node = fb.Select(selector, array_index_i, j);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  VLOG(3) << "Before the transformations: " << f->DumpIr();
  EXPECT_EQ(f->node_count(), 8);
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(false));
  VLOG(3) << "After the transformations: " << f->DumpIr();
  EXPECT_EQ(f->node_count(), 8);
}

TEST_F(SelectLiftingPassTest,
       LiftSingleSelectNotModifiedDueToDifferentInputTypes) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);
  Type* u16_type = p->GetBitsType(32);

  // Create the parameters of the IR function
  BValue a = fb.Param("array", p->GetArrayType(16, u32_type));
  BValue b = fb.Param("array2", p->GetArrayType(16, u16_type));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);
  BValue j = fb.Param("second_index", u32_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i});
  BValue array_index_j = fb.ArrayIndex(b, {j});
  BValue select_node = fb.Select(selector, array_index_i, array_index_j);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  VLOG(3) << "Before the transformations: " << f->DumpIr();
  EXPECT_EQ(f->node_count(), 10);
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(false));
  VLOG(3) << "After the transformations: " << f->DumpIr();
  EXPECT_EQ(f->node_count(), 10);
}

TEST_F(SelectLiftingPassTest, LiftSingleSelectWithMultiIndicesArray) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);

  // Create the parameters of the IR function
  BValue a =
      fb.Param("array", p->GetArrayType(16, p->GetArrayType(8, u32_type)));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);
  BValue j = fb.Param("second_index", u32_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i, j});
  BValue array_index_j = fb.ArrayIndex(a, {i, j});
  BValue select_node = fb.Select(selector, array_index_i, array_index_j);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  EXPECT_EQ(f->node_count(), 9);
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(false));
  EXPECT_EQ(f->node_count(), 9);
}

TEST_F(SelectLiftingPassTest, LiftSingleSelectWithIndicesOfDifferentBitwidth) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);
  Type* u16_type = p->GetBitsType(16);

  // Create the parameters of the IR function
  BValue a = fb.Param("array", p->GetArrayType(16, u32_type));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);
  BValue j = fb.Param("second_index", u16_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i});
  BValue array_index_j = fb.ArrayIndex(a, {j});
  BValue select_node = fb.Select(selector, array_index_i, array_index_j);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  EXPECT_EQ(f->node_count(), 9);
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(false));
  EXPECT_EQ(f->node_count(), 9);
}

TEST_F(SelectLiftingPassTest, LiftSingleSelectWithNoCases) {
  auto p = CreatePackage();
  FunctionBuilder fb(TestName(), p.get());

  // Fetch the types
  Type* u32_type = p->GetBitsType(32);

  // Create the parameters of the IR function
  BValue a = fb.Param("array", p->GetArrayType(16, u32_type));
  BValue c = fb.Param("condition", u32_type);
  BValue i = fb.Param("first_index", u32_type);

  // Create the body of the IR function
  BValue condition_constant = fb.Literal(UBits(10, 32));
  BValue selector = fb.AddCompareOp(Op::kUGt, c, condition_constant);
  BValue array_index_i = fb.ArrayIndex(a, {i});
  std::vector<BValue> cases;
  BValue select_node = fb.Select(selector, cases, array_index_i);

  // Build the function
  XLS_ASSERT_OK_AND_ASSIGN(Function * f, fb.BuildWithReturnValue(select_node));

  // Set the expected outputs
  EXPECT_THAT(Run(f), absl_testing::IsOkAndHolds(false));
}

TEST_F(SelectLiftingPassTest, LiftBinaryOperationSharedLHS) {
  auto p = CreatePackage();
  auto p_expect = CreatePackage();
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_lhs, ParseFunction(R"(
    fn func_lhs(selector: bits[1] id=10, shared: bits[32] id=11, case_a: bits[32] id=12, case_b: bits[32] id=13) -> bits[32] {
      add.14: bits[32] = add(shared, case_a, id=14)
      add.15: bits[32] = add(shared, case_b, id=15)
      ret sel.16: bits[32] = sel(selector, cases=[add.14, add.15], id=16)
    }
  )",
                                                           p.get()));
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_lhs_expect,
                           ParseFunction(R"(
    fn func_lhs(selector: bits[1] id=10, shared: bits[32] id=11, case_a: bits[32] id=12, case_b: bits[32] id=13) -> bits[32] {
      sel.16: bits[32] = sel(selector, cases=[case_a, case_b], id=16)
      ret add_reduced: bits[32] = add(shared, sel.16, id=17)
    }
  )",
                                         p_expect.get()));

  EXPECT_THAT(Run(f_lhs), absl_testing::IsOkAndHolds(true));
  VLOG(3) << "After the transformations:" << f_lhs->DumpIr();
  EXPECT_EQ(f_lhs->node_count(), 6);
  VLOG(3) << f_lhs->DumpIr();
  EXPECT_TRUE(f_lhs->IsDefinitelyEqualTo(f_lhs_expect));
}

TEST_F(SelectLiftingPassTest, LiftBinaryOperationSharedRHSWithDefault) {
  auto p = CreatePackage();
  auto p_expect = CreatePackage();
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_rhs, ParseFunction(R"(
    fn func_rhs(selector: bits[2] id=20, shared: bits[32] id=21, case_a: bits[32] id=22, case_b: bits[32] id=23, default_case: bits[32] id=24) -> bits[32] {
      smul.25: bits[32] = smul(case_a, shared, id=25)
      smul.26: bits[32] = smul(case_b, shared, id=26)
      smul.27: bits[32] = smul(default_case, shared, id=27)
      ret sel.28: bits[32] = sel(selector, cases=[smul.25, smul.26], default=smul.27, id=28)
    }
  )",
                                                           p.get()));
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_rhs_expect,
                           ParseFunction(R"(
    fn func_rhs(selector: bits[2] id=20, shared: bits[32] id=21, case_a: bits[32] id=22, case_b: bits[32] id=23, default_case: bits[32] id=24) -> bits[32] {
      sel.28: bits[32] = sel(selector, cases=[case_a, case_b], default=default_case, id=28)
      ret smul_reduced: bits[32] = smul(sel.28, shared, id=29)
    }
  )",
                                         p_expect.get()));
  EXPECT_THAT(Run(f_rhs), absl_testing::IsOkAndHolds(true));
  VLOG(3) << "After the transformations:" << f_rhs->DumpIr();
  EXPECT_EQ(f_rhs->node_count(), 7);
  VLOG(3) << f_rhs->DumpIr();
  EXPECT_TRUE(f_rhs->IsDefinitelyEqualTo(f_rhs_expect));
}

TEST_F(SelectLiftingPassTest, DontLiftBinaryOpsSharingInconsistentOperandSide) {
  auto p = CreatePackage();
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_not_consistent, ParseFunction(R"(
    fn func_not_consistent(selector: bits[1] id=30, shared: bits[32] id=31, case_a: bits[32] id=32, case_b: bits[32] id=33) -> bits[32] {
      add.34: bits[32] = add(shared, case_a, id=34)
      add.35: bits[32] = add(case_b, shared, id=35)
      ret sel.36: bits[32] = sel(selector, cases=[add.34, add.35], id=36)
    }
  )",
                                                                      p.get()));

  EXPECT_THAT(Run(f_not_consistent), absl_testing::IsOkAndHolds(false));
  VLOG(3) << "After no transformation:" << f_not_consistent->DumpIr();
  EXPECT_EQ(f_not_consistent->node_count(), 7);
}

TEST_F(SelectLiftingPassTest, DontLiftBinaryOpsUsingDifferentOperationTypes) {
  auto p = CreatePackage();
  XLS_ASSERT_OK_AND_ASSIGN(Function * f_different_ops, ParseFunction(R"(
    fn func_different_ops(selector: bits[1] id=40, shared: bits[32] id=41, case_a: bits[32] id=42, case_b: bits[32] id=43) -> bits[32] {
      add.44: bits[32] = add(shared, case_a, id=44)
      sub.45: bits[32] = sub(shared, case_b, id=45)
      ret sel.46: bits[32] = sel(selector, cases=[add.44, sub.45], id=46)
    }
  )",
                                                                     p.get()));

  EXPECT_THAT(Run(f_different_ops), absl_testing::IsOkAndHolds(false));
  VLOG(3) << "After no transformation:" << f_different_ops->DumpIr();
  EXPECT_EQ(f_different_ops->node_count(), 7);
}

}  // namespace

}  // namespace xls
