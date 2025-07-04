// Copyright 2020 The XLS Authors
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

#include "xls/common/math_util.h"

#include <cstdint>
#include <functional>
#include <vector>

#include "absl/types/span.h"

namespace xls {

bool MixedRadixIterate(absl::Span<const int64_t> radix,
                       std::function<bool(const std::vector<int64_t>&)> f) {
  std::vector<int64_t> number;
  number.resize(radix.size(), 0);

  // Returns `true` if there was an overflow or `false` otherwise
  auto increment_number = [&]() -> bool {
    int64_t i = 0;
    while ((i < number.size()) && ((number[i] + 1) >= radix[i])) {
      number[i] = 0;
      ++i;
    }
    if (i < number.size()) {
      ++number[i];
      return false;
    }
    return true;
  };

  do {
    if (f(number)) {
      return true;
    }
  } while (!increment_number());

  return false;
}

}  // namespace xls
