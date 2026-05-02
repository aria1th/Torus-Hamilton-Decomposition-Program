#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

// Direct finite checker for generated all-zero-set 4+2 bridge row covers.
// It mirrors scripts/search_4plus2_kappa_formulas.py for rotation-family
// kappa formulas but avoids materializing the m x m^4 kappa table.

namespace {

struct Formula {
  int a = 0;
  int b = 0;
  int c = 0;
  int d = 0;
  bool reflected = false;
};

struct Model {
  int m = 0;
  int base_size = 0;
  int fiber_size = 0;
  std::vector<std::vector<int>> base_direction;
  std::vector<std::vector<int>> base_next;
  std::vector<int> p_value;
  std::vector<int> zero_count;
  std::vector<int> fiber_forced_q0;
  std::vector<int> fiber_next;
};

constexpr int LAMBDA1[32][5] = {
    {0, 1, 2, 3, 4}, {0, 1, 3, 2, 4}, {0, 1, 2, 4, 3},
    {4, 1, 3, 2, 0}, {4, 1, 2, 3, 0}, {4, 1, 3, 0, 2},
    {1, 0, 2, 4, 3}, {1, 0, 3, 4, 2}, {1, 0, 2, 3, 4},
    {1, 3, 0, 2, 4}, {3, 0, 2, 4, 1}, {4, 3, 0, 2, 1},
    {4, 2, 1, 3, 0}, {4, 3, 1, 0, 2}, {3, 2, 1, 4, 0},
    {0, 1, 2, 3, 4}, {0, 2, 1, 3, 4}, {0, 2, 1, 4, 3},
    {0, 2, 4, 1, 3}, {4, 2, 3, 1, 0}, {2, 4, 1, 3, 0},
    {2, 4, 1, 0, 3}, {2, 0, 4, 1, 3}, {0, 1, 2, 3, 4},
    {1, 0, 3, 2, 4}, {1, 2, 0, 4, 3}, {3, 0, 4, 2, 1},
    {0, 1, 2, 3, 4}, {1, 4, 3, 2, 0}, {0, 1, 2, 3, 4},
    {0, 1, 2, 3, 4}, {0, 1, 2, 3, 4},
};

int positive_mod(int value, int m) {
  int r = value % m;
  return r < 0 ? r + m : r;
}

int pow_int(int base, int exp) {
  int out = 1;
  for (int i = 0; i < exp; ++i) {
    out *= base;
  }
  return out;
}

std::array<int, 4> base_tuple(int index, int m) {
  std::array<int, 4> xs{};
  for (int i = 3; i >= 0; --i) {
    xs[i] = index % m;
    index /= m;
  }
  return xs;
}

int base_index(const std::array<int, 4> &xs, int m) {
  int index = 0;
  for (int value : xs) {
    index = index * m + value;
  }
  return index;
}

std::array<int, 2> fiber_tuple(int index, int m) {
  return {index / m, index % m};
}

int fiber_index(const std::array<int, 2> &ys, int m) {
  return ys[0] * m + ys[1];
}

int lambda1_direction(const std::array<int, 4> &xs, int slot, int m) {
  int full[5] = {xs[0], xs[1], xs[2], xs[3],
                 positive_mod(-(xs[0] + xs[1] + xs[2] + xs[3]), m)};
  int mask = 0;
  for (int i = 0; i < 5; ++i) {
    if (full[(i + 1) % 5] == 0) {
      mask |= (1 << i);
    }
  }
  return LAMBDA1[mask][slot];
}

int count_zeroes(const std::array<int, 4> &xs, int m) {
  int count = 0;
  for (int value : xs) {
    if (value == 0) {
      ++count;
    }
  }
  if (positive_mod(-(xs[0] + xs[1] + xs[2] + xs[3]), m) == 0) {
    ++count;
  }
  return count;
}

std::array<int, 4> add_base_q(std::array<int, 4> xs, int direction, int m) {
  if (direction != 4) {
    xs[direction] = (xs[direction] + 1) % m;
  }
  return xs;
}

std::array<int, 2> add_fiber_q(std::array<int, 2> ys, int direction, int m) {
  if (direction != 2) {
    ys[direction] = (ys[direction] + 1) % m;
  }
  return ys;
}

int d3_odd_direction(int layer, const std::array<int, 2> &ys, int slot, int m) {
  int k_coord = positive_mod(-ys[0] - ys[1] + layer, m);
  if (slot == 0) {
    if (layer == 0 && k_coord != 0) {
      return 1;
    }
    if (layer == 1 % m) {
      return 2;
    }
    return 0;
  }
  if (slot == 1) {
    if (layer == 0) {
      return 2;
    }
    if (layer == 1 % m && k_coord == 0) {
      return 0;
    }
    return 1;
  }
  if (layer == 0 || layer == 1 % m) {
    return k_coord == 0 ? 1 : 0;
  }
  return 2;
}

Model build_model(int m) {
  Model model;
  model.m = m;
  model.base_size = pow_int(m, 4);
  model.fiber_size = m * m;
  model.base_direction.assign(5, std::vector<int>(model.base_size, 0));
  model.base_next.assign(5, std::vector<int>(model.base_size, 0));
  model.p_value.assign(model.base_size, 0);
  model.zero_count.assign(model.base_size, 0);
  for (int base = 0; base < model.base_size; ++base) {
    auto xs = base_tuple(base, m);
    model.p_value[base] = lambda1_direction(xs, 0, m);
    model.zero_count[base] = count_zeroes(xs, m);
    for (int slot = 0; slot < 5; ++slot) {
      int direction = lambda1_direction(xs, slot, m);
      model.base_direction[slot][base] = direction;
      model.base_next[slot][base] = base_index(add_base_q(xs, direction, m), m);
    }
  }

  model.fiber_forced_q0.assign(model.fiber_size, 0);
  model.fiber_next.assign(m * 3 * model.fiber_size, 0);
  for (int fiber = 0; fiber < model.fiber_size; ++fiber) {
    auto ys = fiber_tuple(fiber, m);
    model.fiber_forced_q0[fiber] = fiber_index(add_fiber_q(ys, 0, m), m);
    for (int layer = 0; layer < m; ++layer) {
      for (int slot = 0; slot < 3; ++slot) {
        int direction = d3_odd_direction(layer, ys, slot, m);
        model.fiber_next[(layer * 3 + slot) * model.fiber_size + fiber] =
            fiber_index(add_fiber_q(ys, direction, m), m);
      }
    }
  }
  return model;
}

std::vector<std::vector<int>> parse_rows(const std::string &rows_text, int m) {
  std::vector<std::vector<int>> rows;
  std::string current;
  for (char ch : rows_text) {
    if (ch == ',') {
      if (static_cast<int>(current.size()) != m) {
        throw std::runtime_error("each row must have length m");
      }
      std::vector<int> row;
      for (char digit : current) {
        if (digit < '0' || digit > '6') {
          throw std::runtime_error("row entries must be digits 0..6");
        }
        row.push_back(digit - '0');
      }
      rows.push_back(row);
      current.clear();
    } else if (ch != ' ' && ch != '\n' && ch != '\t') {
      current.push_back(ch);
    }
  }
  if (!current.empty()) {
    if (static_cast<int>(current.size()) != m) {
      throw std::runtime_error("each row must have length m");
    }
    std::vector<int> row;
    for (char digit : current) {
      if (digit < '0' || digit > '6') {
        throw std::runtime_error("row entries must be digits 0..6");
      }
      row.push_back(digit - '0');
    }
    rows.push_back(row);
  }
  if (rows.size() != 7) {
    throw std::runtime_error("expected exactly seven rows");
  }
  for (int layer = 0; layer < m; ++layer) {
    bool seen[7] = {false, false, false, false, false, false, false};
    for (const auto &row : rows) {
      int value = row[layer];
      if (seen[value]) {
        throw std::runtime_error("a column is not a permutation of 0..6");
      }
      seen[value] = true;
    }
  }
  return rows;
}

void apply_map(std::vector<int> &perm, const std::vector<int> &map) {
  for (int &state : perm) {
    state = map[state];
  }
}

void apply_map_ptr(std::vector<int> &perm, const int *map) {
  for (int &state : perm) {
    state = map[state];
  }
}

bool is_single_cycle(const std::vector<int> &perm) {
  std::vector<char> seen(perm.size(), 0);
  int state = 0;
  for (std::size_t step = 0; step < perm.size(); ++step) {
    if (state < 0 || state >= static_cast<int>(perm.size()) || seen[state]) {
      return false;
    }
    seen[state] = 1;
    state = perm[state];
  }
  return state == 0;
}

int selected_slot(const Formula &formula, int layer, int p_value, int zero_count,
                  int component) {
  int r = positive_mod(formula.a * (layer % 3) + formula.b * (p_value % 3) +
                           formula.c * (zero_count % 3) + formula.d,
                       3);
  if (formula.reflected) {
    return positive_mod(r - component, 3);
  }
  return (r + component) % 3;
}

std::tuple<bool, int, std::string> test_formula(
    const Model &model, const std::vector<std::vector<int>> &rows,
    const Formula &formula) {
  std::vector<int> perm(model.fiber_size, 0);
  for (int color = 0; color < 7; ++color) {
    for (int i = 0; i < model.fiber_size; ++i) {
      perm[i] = i;
    }
    int base = 0;
    for (int step = 0; step < model.base_size; ++step) {
      for (int layer = 0; layer < model.m; ++layer) {
        int output_slot = rows[color][layer];
        if (output_slot < 5) {
          int direction = model.base_direction[output_slot][base];
          int next_base = model.base_next[output_slot][base];
          if (direction == 4) {
            int slot = selected_slot(formula, layer, model.p_value[base],
                                     model.zero_count[base], 0);
            apply_map_ptr(
                perm,
                &model.fiber_next[(layer * 3 + slot) * model.fiber_size]);
          } else {
            apply_map(perm, model.fiber_forced_q0);
          }
          base = next_base;
        } else {
          int component = output_slot - 4;
          int slot = selected_slot(formula, layer, model.p_value[base],
                                   model.zero_count[base], component);
          apply_map_ptr(perm,
                        &model.fiber_next[(layer * 3 + slot) * model.fiber_size]);
        }
      }
    }
    if (base != 0) {
      return {false, color, "base section did not return to 0"};
    }
    if (!is_single_cycle(perm)) {
      return {false, color, "fiber section is not a single cycle"};
    }
  }
  return {true, -1, ""};
}

int layer_step(const Model &model, int state, int layer, int output_slot,
               const Formula &formula) {
  int base = state / model.fiber_size;
  int fiber = state % model.fiber_size;
  if (output_slot < 5) {
    int direction = model.base_direction[output_slot][base];
    int next_base = model.base_next[output_slot][base];
    if (direction != 4) {
      fiber = model.fiber_forced_q0[fiber];
    } else {
      int slot = selected_slot(formula, layer, model.p_value[base],
                               model.zero_count[base], 0);
      fiber = model.fiber_next[(layer * 3 + slot) * model.fiber_size + fiber];
    }
    base = next_base;
  } else {
    int component = output_slot - 4;
    int slot = selected_slot(formula, layer, model.p_value[base],
                             model.zero_count[base], component);
    fiber = model.fiber_next[(layer * 3 + slot) * model.fiber_size + fiber];
  }
  return base * model.fiber_size + fiber;
}

int return_step(const Model &model, int state, const std::vector<int> &row,
                const Formula &formula) {
  for (int layer = 0; layer < model.m; ++layer) {
    state = layer_step(model, state, layer, row[layer], formula);
  }
  return state;
}

std::tuple<bool, int, std::string> verify_product_cycles(
    const Model &model, const std::vector<std::vector<int>> &rows,
    const Formula &formula) {
  const int total_states = model.base_size * model.fiber_size;
  std::vector<char> seen(total_states, 0);
  for (int color = 0; color < 7; ++color) {
    std::fill(seen.begin(), seen.end(), 0);
    int state = 0;
    for (int step = 0; step < total_states; ++step) {
      if (state < 0 || state >= total_states) {
        return {false, color, "product state escaped range"};
      }
      if (seen[state]) {
        return {false, color, "product return repeated before full period"};
      }
      seen[state] = 1;
      state = return_step(model, state, rows[color], formula);
    }
    if (state != 0) {
      return {false, color, "product return did not close at full period"};
    }
  }
  return {true, -1, ""};
}

std::string label(const Formula &formula) {
  std::string out = formula.reflected ? "reflected: r = " : "cyclic: r = ";
  out += std::to_string(formula.a) + "*t + " + std::to_string(formula.b) +
         "*p + " + std::to_string(formula.c) + "*z + " +
         std::to_string(formula.d) + " mod 3";
  return out;
}

Formula parse_formula(const std::string &text) {
  Formula formula;
  int values[5] = {0, 0, 0, 0, 0};
  std::string current;
  int index = 0;
  for (char ch : text) {
    if (ch == ',') {
      if (index >= 5) {
        throw std::runtime_error("formula must be a,b,c,d,reflected");
      }
      values[index++] = std::stoi(current);
      current.clear();
    } else if (ch != ' ') {
      current.push_back(ch);
    }
  }
  if (!current.empty()) {
    if (index >= 5) {
      throw std::runtime_error("formula must be a,b,c,d,reflected");
    }
    values[index++] = std::stoi(current);
  }
  if (index != 5) {
    throw std::runtime_error("formula must be a,b,c,d,reflected");
  }
  formula.a = values[0];
  formula.b = values[1];
  formula.c = values[2];
  formula.d = values[3];
  formula.reflected = values[4] != 0;
  return formula;
}

void usage(const char *argv0) {
  std::cerr
      << "usage: " << argv0
      << " --m M --rows ROW0,...,ROW6 [--formula a,b,c,d,reflected]"
      << " [--max-candidates N] [--all-hits] [--verify-product]\n";
}

} // namespace

int main(int argc, char **argv) {
  try {
    int m = 0;
    std::string rows_text;
    bool has_formula = false;
    Formula only_formula;
    int max_candidates = -1;
    bool all_hits = false;
    bool verify_product = false;

    for (int i = 1; i < argc; ++i) {
      std::string arg = argv[i];
      if (arg == "--m" && i + 1 < argc) {
        m = std::stoi(argv[++i]);
      } else if (arg == "--rows" && i + 1 < argc) {
        rows_text = argv[++i];
      } else if (arg == "--formula" && i + 1 < argc) {
        only_formula = parse_formula(argv[++i]);
        has_formula = true;
      } else if (arg == "--max-candidates" && i + 1 < argc) {
        max_candidates = std::stoi(argv[++i]);
      } else if (arg == "--all-hits") {
        all_hits = true;
      } else if (arg == "--verify-product") {
        verify_product = true;
      } else if (arg == "--help") {
        usage(argv[0]);
        return 0;
      } else {
        usage(argv[0]);
        return 2;
      }
    }

    if (m <= 0 || rows_text.empty()) {
      usage(argv[0]);
      return 2;
    }

    auto rows = parse_rows(rows_text, m);
    auto model = build_model(m);
    int checked = 0;
    int hits = 0;

    auto run_formula = [&](const Formula &formula) {
      ++checked;
      auto [ok, color, reason] = test_formula(model, rows, formula);
      if (ok) {
        if (verify_product) {
          auto [product_ok, product_color, product_reason] =
              verify_product_cycles(model, rows, formula);
          if (!product_ok) {
            std::cout << "section-hit product-fail " << checked << ": "
                      << label(formula) << " color=" << product_color
                      << " reason=" << product_reason << "\n";
            return false;
          }
        }
        ++hits;
        std::cout << "hit " << checked << ": " << label(formula) << "\n";
        if (verify_product) {
          std::cout << "product-verified m=" << m
                    << " product_states="
                    << model.base_size * model.fiber_size
                    << " rows=7 return_cycles=single\n";
        }
      } else if (has_formula) {
        std::cout << "fail " << checked << ": " << label(formula)
                  << " color=" << color << " reason=" << reason << "\n";
      }
      return ok;
    };

    if (has_formula) {
      run_formula(only_formula);
    } else {
      for (int reflected_int = 0; reflected_int < 2; ++reflected_int) {
        for (int a = 0; a < 3; ++a) {
          for (int b = 0; b < 3; ++b) {
            for (int c = 0; c < 3; ++c) {
              for (int d = 0; d < 3; ++d) {
                if (max_candidates >= 0 && checked >= max_candidates) {
                  std::cout << "truncated after " << checked << " candidates\n";
                  std::cout << "checked " << checked << " hits " << hits << "\n";
                  return 0;
                }
                Formula formula{a, b, c, d, reflected_int != 0};
                bool ok = run_formula(formula);
                if (ok && !all_hits) {
                  std::cout << "checked " << checked << " hits " << hits << "\n";
                  return 0;
                }
              }
            }
          }
        }
      }
    }

    std::cout << "checked " << checked << " hits " << hits << "\n";
    return hits > 0 || has_formula ? 0 : 1;
  } catch (const std::exception &ex) {
    std::cerr << "error: " << ex.what() << "\n";
    return 2;
  }
}
