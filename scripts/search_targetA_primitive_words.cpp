#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;

struct Model {
  int m;
  int n;
  vector<array<int, 5>> states;
  unordered_map<long long, int> index;
  array<vector<int>, 5> step;

  explicit Model(int mm) : m(mm), n(0) {
    for (int a = 0; a < m; ++a) {
      for (int b = 0; b < m; ++b) {
        for (int c = 0; c < m; ++c) {
          for (int d = 0; d < m; ++d) {
            int e = mod(-(a + b + c + d));
            array<int, 5> w{a, b, c, d, e};
            index[key(w)] = static_cast<int>(states.size());
            states.push_back(w);
          }
        }
      }
    }
    n = static_cast<int>(states.size());
    for (int slot = 0; slot < 5; ++slot) {
      step[slot].assign(n, 0);
    }
    for (int slot = 0; slot < 5; ++slot) {
      for (int id = 0; id < n; ++id) {
        int dir = lambda1_direction(states[id], slot);
        auto y = add_q(states[id], dir);
        step[slot][id] = index.at(key(y));
      }
    }
  }

  int mod(int x) const {
    x %= m;
    return x < 0 ? x + m : x;
  }

  long long key(const array<int, 5> &w) const {
    return (((static_cast<long long>(w[0]) * m + w[1]) * m + w[2]) * m + w[3]);
  }

  array<int, 5> add_q(array<int, 5> w, int dir) const {
    if (dir < 4) {
      w[dir] = mod(w[dir] + 1);
      w[4] = mod(w[4] - 1);
    }
    return w;
  }

  static int rot_mask(int mask, int k) {
    int out = 0;
    for (int x = 0; x < 5; ++x) {
      if (mask & (1 << x)) {
        int y = (x + k) % 5;
        if (y < 0) y += 5;
        out |= 1 << y;
      }
    }
    return out;
  }

  static const array<int, 5> &lambda_rep(int mask) {
    static const unordered_map<int, array<int, 5>> reps{
        {0, {0, 1, 2, 3, 4}},
        {1, {0, 1, 3, 2, 4}},
        {3, {4, 1, 3, 2, 0}},
        {5, {4, 1, 3, 0, 2}},
        {7, {1, 0, 3, 4, 2}},
        {11, {4, 3, 0, 2, 1}},
        {31, {0, 1, 2, 3, 4}},
    };
    auto it = reps.find(mask);
    if (it == reps.end()) {
      throw runtime_error("missing representative");
    }
    return it->second;
  }

  int lambda1(int shifted_mask, int slot) const {
    try {
      return lambda_rep(shifted_mask)[slot];
    } catch (const runtime_error &) {
      for (int k = 0; k < 5; ++k) {
        int rep_mask = rot_mask(shifted_mask, -k);
        try {
          const auto &row = lambda_rep(rep_mask);
          int idx = (slot - k) % 5;
          if (idx < 0) idx += 5;
          return (row[idx] + k) % 5;
        } catch (const runtime_error &) {
        }
      }
    }
    throw runtime_error("no Lambda1 row for mask");
  }

  int lambda1_direction(const array<int, 5> &w, int slot) const {
    int shifted_mask = 0;
    for (int i = 0; i < 5; ++i) {
      if (w[i] == 0) {
        shifted_mask |= 1 << ((i + 4) % 5);
      }
    }
    return lambda1(shifted_mask, slot);
  }

  vector<int> word_perm(const vector<int> &word) const {
    vector<int> perm(n), next(n);
    iota(perm.begin(), perm.end(), 0);
    for (int slot : word) {
      const auto &s = step[slot];
      for (int i = 0; i < n; ++i) {
        next[i] = s[perm[i]];
      }
      perm.swap(next);
    }
    return perm;
  }

  bool single_cycle_word(const vector<int> &word) const {
    vector<int> perm = word_perm(word);
    vector<uint8_t> seen(n, 0);
    int state = 0;
    for (int t = 0; t < n; ++t) {
      if (seen[state]) return false;
      seen[state] = 1;
      state = perm[state];
    }
    return state == 0;
  }
};

string word_string(const vector<int> &word) {
  string out;
  out.reserve(word.size());
  for (int x : word) out.push_back(static_cast<char>('0' + x));
  return out;
}

vector<int> decode_word(uint64_t code, int length) {
  vector<int> word(length, 0);
  for (int i = length - 1; i >= 0; --i) {
    word[i] = static_cast<int>(code % 5);
    code /= 5;
  }
  return word;
}

uint64_t pow5(int length) {
  uint64_t out = 1;
  for (int i = 0; i < length; ++i) out *= 5;
  return out;
}

int main(int argc, char **argv) {
  if (argc < 4) {
    cerr << "usage: " << argv[0]
         << " m max_len limit [min_len=1] [random_samples_per_len=0] [seed=1]\n";
    return 2;
  }
  int m = stoi(argv[1]);
  int max_len = stoi(argv[2]);
  int limit = stoi(argv[3]);
  int min_len = argc > 4 ? stoi(argv[4]) : 1;
  int random_samples = argc > 5 ? stoi(argv[5]) : 0;
  uint64_t seed = argc > 6 ? stoull(argv[6]) : 1;

  Model model(m);
  cerr << "built m=" << m << " states=" << model.n << "\n";
  mt19937_64 rng(seed);
  int hits = 0;

  for (int length = min_len; length <= max_len; ++length) {
    uint64_t total = pow5(length);
    cerr << "length=" << length
         << (random_samples > 0 ? " random_samples=" : " total=")
         << (random_samples > 0 ? random_samples : total) << "\n";
    if (random_samples > 0) {
      uniform_int_distribution<uint64_t> dist(0, total - 1);
      for (int sample = 0; sample < random_samples; ++sample) {
        auto word = decode_word(dist(rng), length);
        if (model.single_cycle_word(word)) {
          cout << "HIT m=" << m << " length=" << length
               << " word=" << word_string(word) << "\n";
          if (++hits >= limit) return 0;
        }
      }
    } else {
      for (uint64_t code = 0; code < total; ++code) {
        auto word = decode_word(code, length);
        if (model.single_cycle_word(word)) {
          cout << "HIT m=" << m << " length=" << length
               << " word=" << word_string(word) << "\n";
          if (++hits >= limit) return 0;
        }
      }
    }
  }
  return 0;
}
