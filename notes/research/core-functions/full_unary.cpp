// Exhaustive research regression, run through check.py --full-unary.
// Packed unary functions use three bits for each nonempty input subset.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

int main() {
  std::set<int> forms;
  for (int a = -1; a < 3; ++a)
    for (int b = -1; b < 3; ++b)
      for (int c = -1; c < 3; ++c) {
        std::array<int, 3> partial{a, b, c};
        if ((a >= 0 && a == b) || (a >= 0 && a == c) || (b >= 0 && b == c)) continue;
        int extra = 7;
        for (int image : partial) if (image >= 0) extra ^= 1 << image;
        for (int x = 1; x < 8; ++x)
          for (int y = 1; y < 8; ++y)
            for (int z = 1; z < 8; ++z) {
              std::array<int, 3> rows{x, y, z};
              bool valid = true;
              for (int i = 0; i < 3; ++i) {
                int mandatory = partial[i] < 0 ? 0 : 1 << partial[i];
                if ((rows[i] & ~(extra | mandatory)) || (rows[i] & mandatory) != mandatory)
                  valid = false;
              }
              if (!valid) continue;
              int code = 0;
              for (int s = 1; s < 8; ++s) {
                int value = extra;
                if ((s & (s - 1)) == 0) {
                  int i = s == 1 ? 0 : s == 2 ? 1 : 2;
                  value = rows[i];
                } else {
                  for (int i = 0; i < 3; ++i)
                    if ((s & (1 << i)) && partial[i] >= 0) value |= 1 << partial[i];
                }
                code |= value << (3 * (s - 1));
              }
              forms.insert(code);
            }
      }
  for (int value = 1; value < 8; ++value) {
    int code = 0;
    for (int i = 0; i < 7; ++i) code |= value << (3 * i);
    forms.insert(code);
  }
  if (forms.size() != 751) return 2;
  std::vector<std::uint8_t> belongs(1 << 21);
  std::vector<std::array<int, 7>> functions;
  for (int code : forms) {
    belongs[code] = 1;
    std::array<int, 7> values{};
    for (int i = 0; i < 7; ++i) values[i] = (code >> (3 * i)) & 7;
    functions.push_back(values);
  }
  // Cross-check the proposed normal forms against the generated unary clone.
  // This closure computation does not use the partial-permutation formula.
  std::vector<std::array<int, 7>> generated;
  std::vector<std::uint8_t> reached(1 << 21);
  auto add = [&](int code) {
    if (reached[code]) return;
    reached[code] = 1;
    std::array<int, 7> values{};
    for (int i = 0; i < 7; ++i) values[i] = (code >> (3 * i)) & 7;
    generated.push_back(values);
  };
  int identity = 0;
  for (int i = 0; i < 7; ++i) identity |= (i + 1) << (3 * i);
  add(identity);
  for (int value = 1; value < 8; ++value) {
    int code = 0;
    for (int i = 0; i < 7; ++i) code |= value << (3 * i);
    add(code);
  }
  for (std::size_t first = 0; first < generated.size(); ++first) {
    const auto a = generated[first];
    std::array<int, 3> permutation{0, 1, 2};
    do {
      int code = 0;
      for (int i = 0; i < 7; ++i) {
        int value = 0;
        for (int r = 0; r < 3; ++r) if (a[i] & (1 << r)) value |= 1 << permutation[r];
        code |= value << (3 * i);
      }
      add(code);
    } while (std::next_permutation(permutation.begin(), permutation.end()));
    for (std::size_t second = 0; second < generated.size(); ++second) {
      const auto b = generated[second];
      for (int owner = 1; owner < 8; owner *= 2) {
        int code = 0;
        for (int i = 0; i < 7; ++i)
          code |= (a[i] == owner || b[i] == owner ? owner : a[i] | b[i]) << (3 * i);
        add(code);
      }
    }
  }
  if (generated.size() != forms.size()) return 2;
  for (int code : forms) if (!reached[code]) return 2;
  int count;
  if (!(std::cin >> count)) return 3;
  for (int test = 0; test < count; ++test) {
    std::array<int, 343> table{};
    for (int &x : table) if (!(std::cin >> x) || x < 1 || x > 7) return 3;
    std::uint64_t checked = 0;
    for (const auto &a : functions)
      for (const auto &b : functions) {
        int offset[7];
        for (int i = 0; i < 7; ++i) offset[i] = (a[i] - 1) * 49 + (b[i] - 1) * 7 - 1;
        for (const auto &c : functions) {
          int code = 0;
          for (int i = 0; i < 7; ++i) code |= table[offset[i] + c[i]] << (3 * i);
          if (!belongs[code]) {
            std::cerr << "Substitution outside the unary fragment in test " << test << '\n';
            return 1;
          }
          ++checked;
        }
      }
    std::cout << "Full-unary substitution test " << test << ": " << checked
              << " triples preserve the 751-function fragment.\n";
  }
}
