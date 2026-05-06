#include <bits/stdc++.h>
using namespace std;

int PERT_rows[32][5];
pair<int, int> CAN[32];

int rotmask(int mask, int k) {
    int out = 0;
    for (int x = 0; x < 5; x++) {
        if (mask & (1 << x)) out |= 1 << ((x + k + 50) % 5);
    }
    return out;
}

void init() {
    int reps[] = {0, 1, 3, 5, 7, 11, 31};
    int rows[][5] = {
        {0, 1, 2, 3, 4},
        {0, 1, 3, 2, 4},
        {4, 1, 3, 2, 0},
        {4, 1, 3, 0, 2},
        {1, 0, 3, 4, 2},
        {4, 0, 3, 2, 1},
        {0, 1, 2, 3, 4},
    };
    memset(PERT_rows, -1, sizeof(PERT_rows));
    for (int r = 0; r < 7; r++) {
        for (int j = 0; j < 5; j++) PERT_rows[reps[r]][j] = rows[r][j];
    }
    int row7[5] = {1, 4, 3, 0, 2};
    int row11[5] = {4, 0, 3, 2, 1};
    for (int j = 0; j < 5; j++) {
        PERT_rows[7][j] = row7[j];
        PERT_rows[11][j] = row11[j];
    }
    for (int mask = 0; mask < 32; mask++) {
        for (int k = 0; k < 5; k++) {
            int rep = rotmask(mask, -k);
            bool ok = false;
            for (int r : reps) ok = ok || (rep == r);
            if (ok) {
                CAN[mask] = {rep, k};
                break;
            }
        }
    }
}

inline int lambdaE(int S, int c) {
    auto [rep, k] = CAN[S];
    return (PERT_rows[rep][(c - k + 5) % 5] + k) % 5;
}

inline int shifted_zero_mask(const array<int, 5>& w) {
    int S = 0;
    for (int i = 0; i < 5; i++) if (w[i] == 0) S |= 1 << ((i + 4) % 5);
    return S;
}

inline int p_s(const array<int, 5>& w, int slot) {
    return lambdaE(shifted_zero_mask(w), slot);
}

inline array<int, 5> theta_state(int m, int slot, int a) {
    array<int, 5> w = {0, 0, 0, 0, 0};
    w[(1 + slot) % 5] = a % m;
    w[(4 + slot) % 5] = (m - a) % m;
    return w;
}

inline int theta_param(int m, int slot, const array<int, 5>& w) {
    int a = w[(1 + slot) % 5];
    if (a == 0) return -1;
    return theta_state(m, slot, a) == w ? a : -1;
}

inline void step(int m, int slot, const array<int, 5>& nu, array<int, 5>& w) {
    int p = p_s(w, slot);
    for (int i = 0; i < 5; i++) {
        w[i] += nu[i];
        w[i] %= m;
    }
    if (++w[p] == m) w[p] = 0;
}

inline uint64_t encode4(int m, const array<int, 5>& w) {
    uint64_t x = 0;
    for (int i = 0; i < 4; i++) x = x * (uint64_t)m + (uint64_t)w[i];
    return x;
}

struct Check {
    bool ok = false;
    bool start_ok = true;
    bool no_return = false;
    bool cap_hit = false;
    bool repeat_hit = false;
    long long time_sum = 0;
    vector<int> cycles;
    vector<array<int, 3>> blocks; // start, end, delta
};

Check check_candidate(int m, int slot, const array<int, 5>& nu, long long cap) {
    Check out;
    int N = m - 1;
    vector<int> V(N + 1, -1);
    vector<long long> times(N + 1, 0);
    int seam_port = (slot + 2) % 5;
    long long max_steps = cap > 0 ? cap : 1LL * m * m * m * m + 5;

    for (int a = 1; a < m; a++) {
        auto w = theta_state(m, slot, a);
        if (p_s(w, slot) != seam_port) out.start_ok = false;
        unordered_set<uint64_t> seen;
        seen.reserve(1024);
        seen.insert(encode4(m, w));
        bool returned = false;
        for (long long t = 1; t <= max_steps; t++) {
            step(m, slot, nu, w);
            int b = theta_param(m, slot, w);
            if (b >= 1) {
                V[a] = b;
                times[a] = t;
                out.time_sum += t;
                returned = true;
                break;
            }
            uint64_t code = encode4(m, w);
            if (seen.find(code) != seen.end()) {
                out.repeat_hit = true;
                break;
            }
            if (cap > 0) seen.insert(code);
        }
        if (!returned) {
            out.no_return = true;
            if (!out.repeat_hit) out.cap_hit = true;
            return out;
        }
    }

    vector<int> seen(N + 1, 0);
    for (int a = 1; a < m; a++) {
        if (seen[a]) continue;
        int x = a, L = 0;
        while (!seen[x]) {
            seen[x] = 1;
            L++;
            x = V[x];
            if (x < 1 || x >= m) {
                out.no_return = true;
                return out;
            }
        }
        out.cycles.push_back(L);
    }
    sort(out.cycles.begin(), out.cycles.end(), greater<int>());

    int start = 1, prev = 1, cur_delta = (V[1] - 1 + m) % m;
    for (int a = 2; a < m; a++) {
        int delta = (V[a] - a + m) % m;
        if (delta != cur_delta) {
            out.blocks.push_back({start, prev, cur_delta});
            start = a;
            cur_delta = delta;
        }
        prev = a;
    }
    out.blocks.push_back({start, prev, cur_delta});
    out.ok = out.start_ok && out.cycles.size() == 1 && out.cycles[0] == N
        && out.time_sum == 1LL * m * m * m * m;
    return out;
}

vector<int> parse_pattern(const string& s) {
    vector<int> out;
    string cur;
    for (char ch : s) {
        if (ch == ',') {
            if (!cur.empty()) out.push_back(stoi(cur));
            cur.clear();
        } else {
            cur.push_back(ch);
        }
    }
    if (!cur.empty()) out.push_back(stoi(cur));
    sort(out.begin(), out.end());
    out.erase(unique(out.begin(), out.end()), out.end());
    return out;
}

void gen_counts_rec(
    int total, const vector<int>& pat, int pos, array<int, 5>& nu,
    const function<void(const array<int, 5>&)>& emit
) {
    int left = (int)pat.size() - pos;
    if (left == 1) {
        if (total >= 1) {
            nu[pat[pos]] = total;
            emit(nu);
            nu[pat[pos]] = 0;
        }
        return;
    }
    for (int v = 1; v <= total - left + 1; v++) {
        nu[pat[pos]] = v;
        gen_counts_rec(total - v, pat, pos + 1, nu, emit);
        nu[pat[pos]] = 0;
    }
}

int main(int argc, char** argv) {
    init();
    if (argc < 5) {
        cerr << "usage: fast_d5_routeE_small_seam_search m support-pattern max_hits cap_steps [candidate_limit]\n";
        cerr << "example: fast_d5_routeE_small_seam_search 86 0,3,4 5 0\n";
        return 1;
    }
    int m = atoi(argv[1]);
    vector<int> pat = parse_pattern(argv[2]);
    int max_hits = atoi(argv[3]);
    long long cap = atoll(argv[4]);
    long long candidate_limit = argc >= 6 ? atoll(argv[5]) : 0;
    int slot = 0;
    long long checked = 0, hits = 0, cap_hit = 0, repeat_hit = 0;
    array<int, 5> nu = {0, 0, 0, 0, 0};
    cout << "m,pattern,checked,counts,ok,cycles,time_sum,m4,block_count,max_block,blocks_prefix\n";
    gen_counts_rec(m - 1, pat, 0, nu, [&](const array<int, 5>& cand) {
        if (max_hits > 0 && hits >= max_hits) return;
        if (candidate_limit && checked >= candidate_limit) return;
        checked++;
        Check chk = check_candidate(m, slot, cand, cap);
        cap_hit += chk.cap_hit ? 1 : 0;
        repeat_hit += chk.repeat_hit ? 1 : 0;
        if (chk.ok) {
            hits++;
            int max_block = 0;
            for (auto b : chk.blocks) max_block = max(max_block, b[1] - b[0] + 1);
            cout << m << ",\"" << argv[2] << "\"," << checked << ",\"";
            for (int i = 0; i < 5; i++) {
                if (i) cout << ' ';
                cout << cand[i];
            }
            cout << "\",1,\"";
            for (size_t i = 0; i < chk.cycles.size(); i++) {
                if (i) cout << ' ';
                cout << chk.cycles[i];
            }
            cout << "\"," << chk.time_sum << "," << 1LL * m * m * m * m
                 << "," << chk.blocks.size() << "," << max_block << ",\"";
            for (size_t i = 0; i < chk.blocks.size() && i < 10; i++) {
                if (i) cout << ';';
                auto b = chk.blocks[i];
                cout << b[0] << '-' << b[1] << ':' << b[2];
            }
            cout << "\"\n";
            cout.flush();
        }
    });
    cerr << "summary m=" << m << " pattern=" << argv[2]
         << " checked=" << checked << " hits=" << hits
         << " cap_hit=" << cap_hit << " repeat_hit=" << repeat_hit << "\n";
}
