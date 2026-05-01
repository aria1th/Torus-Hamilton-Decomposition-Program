#include <bits/stdc++.h>
using namespace std;

int PERT_rows[32][5];
pair<int, int> CAN[32];

int rotmask(int mask, int k) {
    int R = 0;
    for (int x = 0; x < 5; x++) {
        if (mask & (1 << x)) {
            R |= 1 << ((x + k + 50) % 5);
        }
    }
    return R;
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
    for (int i = 0; i < 32; i++) {
        for (int j = 0; j < 5; j++) {
            PERT_rows[i][j] = -1;
        }
    }
    for (int r = 0; r < 7; r++) {
        for (int j = 0; j < 5; j++) {
            PERT_rows[reps[r]][j] = rows[r][j];
        }
    }
    int row7[5] = {1, 4, 3, 0, 2};
    int row11[5] = {4, 0, 3, 2, 1};
    for (int j = 0; j < 5; j++) {
        PERT_rows[7][j] = row7[j];
        PERT_rows[11][j] = row11[j];
    }
    for (int mask = 0; mask < 32; mask++) {
        for (int k = 0; k < 5; k++) {
            int R = rotmask(mask, -k);
            bool is_rep = false;
            for (int rep : reps) {
                if (R == rep) {
                    is_rep = true;
                }
            }
            if (is_rep) {
                CAN[mask] = {R, k};
                break;
            }
        }
    }
}

inline int LambdaE(int S, int c) {
    auto [rep, k] = CAN[S];
    return (PERT_rows[rep][(c - k + 5) % 5] + k) % 5;
}

inline int shifted_zero_mask(array<int, 5> w) {
    int S = 0;
    for (int i = 0; i < 5; i++) {
        if (w[i] == 0) {
            S |= 1 << ((i + 4) % 5);
        }
    }
    return S;
}

inline int p_s(array<int, 5> w, int slot) {
    return LambdaE(shifted_zero_mask(w), slot);
}

inline array<int, 5> step(int m, array<int, 5> nu, int slot, array<int, 5> w) {
    int p = p_s(w, slot);
    for (int i = 0; i < 5; i++) {
        w[i] = (w[i] + nu[i]) % m;
    }
    w[p]++;
    if (w[p] == m) {
        w[p] = 0;
    }
    return w;
}

array<int, 5> theta_state(int m, int slot, int a) {
    array<int, 5> w = {0, 0, 0, 0, 0};
    w[(1 + slot) % 5] = a % m;
    w[(4 + slot) % 5] = (m - a) % m;
    return w;
}

int theta_param(int m, int slot, array<int, 5> w) {
    int a = w[(1 + slot) % 5];
    if (a == 0) {
        return -1;
    }
    array<int, 5> z = theta_state(m, slot, a);
    return z == w ? a : -1;
}

int main(int argc, char **argv) {
    init();
    if (argc < 8) {
        cerr << "usage: fast_d5_routeE_small_seam_verify m slot n0 n1 n2 n3 n4\n";
        return 1;
    }
    int m = atoi(argv[1]);
    int slot = atoi(argv[2]);
    array<int, 5> nu;
    for (int i = 0; i < 5; i++) {
        nu[i] = atoi(argv[3 + i]);
    }

    int N = m - 1;
    vector<int> V(N + 1, -1);
    vector<long long> times(N + 1, 0);
    long long sum = 0;
    bool start_ok = true;
    int j = (slot + 2) % 5;
    for (int a = 1; a < m; a++) {
        auto w = theta_state(m, slot, a);
        if (p_s(w, slot) != j) {
            start_ok = false;
        }
        long long maxsteps = 1LL * m * m * m * m + 5;
        long long t;
        for (t = 1; t <= maxsteps; t++) {
            w = step(m, nu, slot, w);
            int b = theta_param(m, slot, w);
            if (b >= 1) {
                V[a] = b;
                times[a] = t;
                sum += t;
                break;
            }
        }
        if (t > maxsteps) {
            cout << "NO_RETURN a " << a << "\n";
            return 0;
        }
    }

    vector<int> seen(N + 1, 0);
    vector<int> cycles;
    for (int a = 1; a < m; a++) {
        if (seen[a]) {
            continue;
        }
        int x = a;
        int L = 0;
        while (!seen[x]) {
            seen[x] = 1;
            L++;
            x = V[x];
            if (x < 1 || x >= m) {
                cerr << "bad V\n";
                return 1;
            }
        }
        cycles.push_back(L);
    }
    sort(cycles.begin(), cycles.end());

    map<long long, int> dist;
    for (int a = 1; a < m; a++) {
        dist[times[a]]++;
    }

    bool ok = start_ok && cycles.size() == 1 && cycles[0] == N &&
        sum == 1LL * m * m * m * m;
    cout << "m " << m << " slot " << slot << " j " << j << " counts";
    for (int x : nu) {
        cout << " " << x;
    }
    cout << " start_ok " << start_ok << " cycles";
    for (int L : cycles) {
        cout << " " << L;
    }
    cout << " sum " << sum << " m4 " << 1LL * m * m * m * m
         << " ok " << ok << "\n";

    cout << "dist";
    int k = 0;
    for (auto &kv : dist) {
        if (k++ < 25) {
            cout << " (" << kv.first << "," << kv.second << ")";
        }
    }
    cout << "\n";

    cout << "map";
    for (int a = 1; a < min(m, 15); a++) {
        cout << " " << a << "->" << V[a] << ":" << times[a];
    }
    cout << "\n";
}
