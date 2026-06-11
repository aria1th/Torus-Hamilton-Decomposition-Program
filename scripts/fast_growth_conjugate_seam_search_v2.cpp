// fast_growth_conjugate_seam_search_v2.cpp
//
// V2 of the STEP-2 seam annealer (see fast_growth_conjugate_seam_search.cpp
// for the v1 baseline; this file is a copy with design-route guidance from
// design_growth_seam_closed_form.py / growth_seam_design_ledger_m4.json
// wired into the move generator).  The evaluator, plan JSON format, energy,
// --check-plan output, hit path and atomic cache-free hit write are all
// UNCHANGED from v1 (byte-compatible); hits close through
// search_growth_conjugate_repair.py --verify-hit exactly as before.
//
// V2 ADDITIONS (each individually toggleable):
//  (G3) parity early-reject: per-(layer,color) permutation signs are cached
//       by row hash; sign(return_c) = prod_t sign(L_{t,c}) is exact (sign
//       is a homomorphism), so a proposal's parity penalty (3000 per +1
//       sign) plus 400*skipped is a lower bound on its energy known BEFORE
//       the nine compose-counts.  The Metropolis draw is taken once and
//       shared, so early rejection is statistically identical to full
//       evaluation.  Predicted signs are cross-checked against the
//       evaluator on every full eval (mismatch counter; observed 0).
//                                                      [--no-early-reject]
//  (G2) keep-coverage repair pass as a move POST-condition: donation cell
//       conflicts are re-offset (or dropped) instead of skipped at +400,
//       stairs are moved off donated columns, and gated donor keep-coverage
//       (every (z0,z1) storey of every donated column must keep an ungated
//       movable layer for its donor color: ledger guidance (ii)) is
//       repaired by dropping an offending donation.    [--no-repair]
//  (G1) leaf-word color-purity bias: new donations prefer the target
//       leaf's dominant donated color, deletions prefer minority colors
//       (full mixed-color leaf words are never single: ledger T2b).
//                                                      [--no-purity]
//  (M)  leaf-merge move class: with prob --merge-prob (default 0.10) the
//       proposal builds the current plan, labels the worst leaf's return
//       cycles, and searches for a leaf staircase whose m gated cells
//       straddle >= 2 distinct cycles (a boundary swap that can merge
//       them), proposing that stair directly.
//
// BUILD:   g++ -O2 -o fast_growth_conjugate_seam_search_v2 \
//              fast_growth_conjugate_seam_search_v2.cpp
// PREP:    python3 dump_growth_conjugate_base.py [--m 4|6]   (same as v1)
// CHECK:   ./fast_growth_conjugate_seam_search_v2 --check-plan PLAN.json ...
//          (byte-identical output to v1 --check-plan on the same files;
//           validated 2026-06-11, see growth_conjugate_v2_notes.json)
// ANNEAL:  ./fast_growth_conjugate_seam_search_v2 --anneal --m 4 --seed S \
//              --iters N --restarts R [--resume PLAN.json] \
//              [--leaf-weight W] [--tau T] [--tag TAG] [--merge-prob P]
//              [--no-early-reject] [--no-repair] [--no-purity]
//          best-so-far -> growth_conjugate_best_m{m}_cpp_{TAG}.json,
//          a full hit (E == 0, re-verified cache-free) ->
//          growth_conjugate_hit_m{m}.json (atomic; plus a per-tag copy).
//
// Run from the scripts/ directory (default paths are relative).

#include <bits/stdc++.h>
using namespace std;
typedef uint8_t u8;
typedef uint32_t u32;
typedef uint64_t u64;

// ----------------------------------------------------------- v2 feature flags
static bool g_earlyReject = true;   // (G3) parity early-reject
static bool g_repair = true;        // (G2) keep-coverage repair pass
static bool g_purity = true;        // (G1) leaf color-purity move bias
static double g_mergeProb = 0.10;   // (M)  leaf-merge move probability

// --------------------------------------------------------------- tiny JSON
struct JV {
    enum T { NUM, STR, ARR, OBJ, BOOL, NUL } t = NUL;
    double num = 0;
    string str;
    vector<JV> arr;
    vector<pair<string, JV>> obj;
    const JV* get(const string& k) const {
        for (auto& kv : obj) if (kv.first == k) return &kv.second;
        return nullptr;
    }
    long long i() const { return llround(num); }
};

struct JParser {
    const string& s; size_t p = 0;
    JParser(const string& src) : s(src) {}
    void ws() { while (p < s.size() && isspace((u8)s[p])) p++; }
    [[noreturn]] void die(const string& msg) {
        fprintf(stderr, "json parse error at %zu: %s\n", p, msg.c_str());
        exit(1);
    }
    JV parse() {
        ws();
        if (p >= s.size()) die("eof");
        char c = s[p];
        JV v;
        if (c == '{') {
            v.t = JV::OBJ; p++;
            ws();
            if (s[p] == '}') { p++; return v; }
            while (true) {
                ws();
                if (s[p] != '"') die("key");
                string k = pstr();
                ws();
                if (s[p] != ':') die("colon");
                p++;
                v.obj.push_back({k, parse()});
                ws();
                if (s[p] == ',') { p++; continue; }
                if (s[p] == '}') { p++; break; }
                die("obj sep");
            }
        } else if (c == '[') {
            v.t = JV::ARR; p++;
            ws();
            if (s[p] == ']') { p++; return v; }
            while (true) {
                v.arr.push_back(parse());
                ws();
                if (s[p] == ',') { p++; continue; }
                if (s[p] == ']') { p++; break; }
                die("arr sep");
            }
        } else if (c == '"') {
            v.t = JV::STR; v.str = pstr();
        } else if (c == 't') { v.t = JV::BOOL; v.num = 1; p += 4; }
        else if (c == 'f') { v.t = JV::BOOL; v.num = 0; p += 5; }
        else if (c == 'n') { v.t = JV::NUL; p += 4; }
        else {
            v.t = JV::NUM;
            size_t q = p;
            while (q < s.size() && (isdigit((u8)s[q]) || strchr("+-.eE", s[q])))
                q++;
            v.num = atof(s.substr(p, q - p).c_str());
            p = q;
        }
        return v;
    }
    string pstr() {
        p++; string out;
        while (p < s.size() && s[p] != '"') {
            if (s[p] == '\\') { p++; out.push_back(s[p]); }
            else out.push_back(s[p]);
            p++;
        }
        p++;
        return out;
    }
};

string slurp(const string& path) {
    ifstream f(path, ios::binary);
    if (!f) { fprintf(stderr, "cannot open %s\n", path.c_str()); exit(1); }
    stringstream ss; ss << f.rdbuf();
    return ss.str();
}

// ----------------------------------------------------------------- plan
struct Don { int axis, t, c, start, a; };
struct Stair { int t, x, b; };
struct Wild { int t, x, c, lay; array<int, 3> sigma; };
struct Line { int t, x, xi, c; };
struct Oswap { int t, c, c2, x0; };
struct Plan {
    vector<Don> dons;
    vector<Stair> stairs;
    vector<Wild> wilds;
    vector<Line> lines;
    vector<Oswap> oswaps;
};

// ----------------------------------------------------------------- engine
struct Engine {
    int d, m, K, K2, NCOL, NU0, NU1;
    vector<long long> powm;                  // m^0..m^5
    vector<vector<u8>> dirs;                 // [t*d+c][x] base reads 0..6
    vector<array<int, 2>> cross0;            // per color (t, x)
    vector<array<int, 3>> cross1;            // per color (t, x, xi)
    vector<vector<u8>> wilds;                // [lay][(z0*m+z1)*3+j] in {0,1,2}
    vector<vector<u32>> addt;                // [v 0..d+1][i in K2]
    vector<vector<vector<int>>> orbits;      // [t*d+c] -> list of cycles >= 2
    unordered_map<u64, int> orbIndex;        // (t,c,start) -> orbit pos
    int tau_s = 0;
    vector<vector<u8>> tmpl, child;          // [t*NCOL+c][i in K2]
    vector<char> touched;
    vector<int> touchedList;
    vector<u64> tmplHash, curHash;
    vector<unordered_map<u64, pair<int, int>>> retCache;  // per color
    unordered_map<u64, vector<int>> closureCache;         // empty = None
    unordered_set<u64> closureNone;
    vector<u32> scratchR;
    vector<u64> scratchVis;
    long long evalsDone = 0, colorsComputed = 0;
    // ---- v2 state ----
    unordered_map<u64, int> rowSignCache;    // row hash -> layer-perm sign
    vector<u8> movMask;                      // [c*K+x] bitmask of movable t
    long long earlyRejects = 0, signMismatch = 0, layerSignsComputed = 0;
    // flat scratch for the repair pass (plans can carry 100+ donations;
    // hash sets are far too slow there)
    vector<u64> repClaim;                    // m*NCOL*K2 bits, cell claims
    vector<u8> repDonCol;                    // m*K, donated columns
    vector<u8> repG0, repG1;                 // m*d*K storey gate masks
    vector<u8> repCxSeen;                    // d*K donated (c,x) dedupe

    static u64 hashBytes(const u8* p, size_t n) {
        u64 h = 1469598103934665603ULL;
        size_t i = 0;
        for (; i + 8 <= n; i += 8) {
            u64 k; memcpy(&k, p + i, 8);
            h ^= k; h *= 0x100000001b3ULL; h ^= h >> 29;
        }
        for (; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ULL; }
        return h;
    }

    void loadBase(const string& path) {
        string raw = slurp(path);
        const u8* p = (const u8*)raw.data();
        auto rd32 = [&]() { int v; memcpy(&v, p, 4); p += 4; return v; };
        u32 magic = (u32)rd32();
        if (magic != 0x47434231u) { fprintf(stderr, "bad magic\n"); exit(1); }
        d = rd32(); m = rd32();
        K = 1; for (int i = 0; i < d - 1; i++) K *= m;
        K2 = K * m * m;
        NCOL = d + 2; NU0 = d; NU1 = d + 1;
        powm.resize(d - 1);
        powm[0] = 1;
        for (int i = 1; i < d - 1; i++) powm[i] = powm[i - 1] * m;
        dirs.assign(m * d, vector<u8>(K));
        for (int t = 0; t < m; t++)
            for (int c = 0; c < d; c++) {
                memcpy(dirs[t * d + c].data(), p, K); p += K;
            }
        cross0.resize(d); cross1.resize(d);
        for (int c = 0; c < d; c++) {
            cross0[c][0] = rd32(); cross0[c][1] = rd32();
        }
        for (int c = 0; c < d; c++) {
            cross1[c][0] = rd32(); cross1[c][1] = rd32(); cross1[c][2] = rd32();
        }
        int nw = rd32();
        wilds.assign(nw, vector<u8>(m * m * 3));
        for (int w = 0; w < nw; w++) {
            memcpy(wilds[w].data(), p, m * m * 3); p += m * m * 3;
        }
        buildAdd();
        buildOrbits();
        scratchR.resize(K2);
        scratchVis.resize((K2 + 63) / 64);
        retCache.assign(NCOL, {});
        // v2: movable-layer bitmask per (color, column) for keep-coverage
        movMask.assign(d * K, 0);
        for (int t = 0; t < m; t++)
            for (int c = 0; c < d; c++)
                for (int x = 0; x < K; x++)
                    if (dirs[t * d + c][x] < d - 1)
                        movMask[c * K + x] |= (u8)(1 << t);
        repClaim.assign(((size_t)m * NCOL * K2 + 63) / 64, 0);
        repDonCol.assign(m * K, 0);
        repG0.assign(m * d * K, 0);
        repG1.assign(m * d * K, 0);
        repCxSeen.assign(d * K, 0);
    }

    void buildAdd() {
        // child directions: v < d-1 add e_v in the low K part; v = d-1 (D0)
        // steps z0; v = d (D1) steps z1; v = d+1 (LAST) is the identity.
        addt.assign(NCOL, vector<u32>(K2));
        for (int i = 0; i < K2; i++) {
            int x = i % K, z0 = (i / K) % m, z1 = i / (K * m);
            for (int v = 0; v < d - 1; v++) {
                long long pw = powm[v];
                int dig = (int)((x / pw) % m);
                int xx = dig < m - 1 ? x + (int)pw : x - (int)((m - 1) * pw);
                addt[v][i] = xx + K * z0 + K * m * z1;
            }
            addt[d - 1][i] = x + K * ((z0 + 1) % m) + K * m * z1;
            addt[d][i] = x + K * z0 + K * m * ((z1 + 1) % m);
            addt[d + 1][i] = i;
        }
    }

    int stepBase(int t, int c, int x) const {       // base layer map on K
        int v = dirs[t * d + c][x];
        if (v == d - 1) return x;
        long long pw = powm[v];
        int dig = (int)((x / pw) % m);
        return dig < m - 1 ? x + (int)pw : x - (int)((m - 1) * pw);
    }

    void buildOrbits() {
        orbits.assign(m * d, {});
        for (int t = 0; t < m; t++)
            for (int c = 0; c < d; c++) {
                vector<char> seen(K, 0);
                auto& out = orbits[t * d + c];
                for (int s = 0; s < K; s++) {
                    if (seen[s]) continue;
                    vector<int> cyc{s};
                    seen[s] = 1;
                    int x = stepBase(t, c, s);
                    while (x != s) { cyc.push_back(x); seen[x] = 1; x = stepBase(t, c, x); }
                    if ((int)cyc.size() >= 2) {
                        orbIndex[orbKey(t, c, cyc[0])] = (int)out.size();
                        out.push_back(move(cyc));
                    }
                }
            }
    }

    u64 orbKey(int t, int c, int start) const {
        return ((u64)(t * 16 + c) << 32) | (u32)start;
    }
    const vector<int>* findOrbit(int t, int c, int start) const {
        auto it = orbIndex.find(orbKey(t, c, start));
        if (it == orbIndex.end()) return nullptr;
        return &orbits[t * d + c][it->second];
    }

    // ---- template: grow_two_crossings + tau_s leaf-role swap -------------
    void buildTemplate(int tau) {
        tau_s = tau;
        map<pair<int, int>, int> planes;     // (t,x) -> 1
        map<pair<int, int>, int> lines;      // (t,x) -> xi
        for (int c = 0; c < d; c++) {
            auto [t, x] = pair<int, int>(cross0[c][0], cross0[c][1]);
            if (dirs[t * d + c][x] != d - 1) {
                fprintf(stderr, "cross0 color %d not at a zero read\n", c);
                exit(1);
            }
            planes.emplace(make_pair(t, x), 1);
        }
        for (int c = 0; c < d; c++) {
            int t = cross1[c][0], x = cross1[c][1], xi = cross1[c][2];
            if (dirs[t * d + c][x] != d - 1 || planes.count({t, x})) {
                fprintf(stderr, "cross1 color %d invalid\n", c);
                exit(1);
            }
            lines.emplace(make_pair(t, x), xi);
        }
        int D0 = d - 1, D1 = d, LAST = d + 1;
        tmpl.assign(m * NCOL, vector<u8>(K2));
        vector<int> base(NCOL), reads(NCOL);
        for (int t = 0; t < m; t++) {
            for (int x = 0; x < K; x++) {
                for (int c = 0; c < d; c++) {
                    int v = dirs[t * d + c][x];
                    base[c] = v < d - 1 ? v : LAST;
                }
                base[NU0] = D0; base[NU1] = D1;
                bool onp = planes.count({t, x});
                auto lit = lines.find({t, x});
                int xi = lit == lines.end() ? -1 : lit->second;
                for (int z0 = 0; z0 < m; z0++) {
                    for (int c = 0; c < NCOL; c++) reads[c] = base[c];
                    if (onp) {
                        for (int c = 0; c < NCOL; c++) {
                            if (reads[c] == LAST) reads[c] = D0;
                            else if (reads[c] == D0) reads[c] = LAST;
                        }
                    } else if (xi >= 0 && z0 == xi) {
                        for (int c = 0; c < NCOL; c++) {
                            if (reads[c] == LAST) reads[c] = D1;
                            else if (reads[c] == D1) reads[c] = LAST;
                        }
                    }
                    for (int z1 = 0; z1 < m; z1++) {
                        int i = x + K * z0 + K * m * z1;
                        for (int c = 0; c < NCOL; c++)
                            tmpl[t * NCOL + c][i] = (u8)reads[c];
                    }
                }
            }
        }
        swap(tmpl[tau_s * NCOL + NU0], tmpl[tau_s * NCOL + NU1]);
        child = tmpl;
        touched.assign(m * NCOL, 0);
        touchedList.clear();
        tmplHash.resize(m * NCOL);
        for (int r = 0; r < m * NCOL; r++)
            tmplHash[r] = hashBytes(tmpl[r].data(), K2);
        curHash = tmplHash;
        for (auto& mp : retCache) mp.clear();
    }

    void own(int t, int c) {
        int r = t * NCOL + c;
        if (!touched[r]) { touched[r] = 1; touchedList.push_back(r); }
    }
    void restore() {
        for (int r : touchedList) {
            memcpy(child[r].data(), tmpl[r].data(), K2);
            touched[r] = 0;
            curHash[r] = tmplHash[r];
        }
        touchedList.clear();
    }

    // ---- construction pieces (full check pass, then apply pass) ----------
    bool donate(int t, int c, const vector<int>& cyc, int a, int axis,
                int leaf) {
        int dflt = axis == 0 ? d - 1 : d;
        int L = (int)cyc.size();
        int q = m / __gcd(L, m);
        int n = q * L;
        u8* rowL = child[t * NCOL + leaf].data();
        u8* rowC = child[t * NCOL + c].data();
        const u8* dc = dirs[t * d + c].data();
        for (int j = 0; j < n; j++) {
            int x = cyc[j % L], w = ((a - j) % m + m) % m;
            int v = dc[x];
            if (v >= d - 1) return false;
            for (int z = 0; z < m; z++) {
                int i = axis == 0 ? x + K * w + K * m * z
                                  : x + K * z + K * m * w;
                if (rowL[i] != dflt || rowC[i] != v) return false;
            }
        }
        for (int j = 0; j < n; j++) {
            int x = cyc[j % L], w = ((a - j) % m + m) % m;
            int v = dc[x];
            for (int z = 0; z < m; z++) {
                int i = axis == 0 ? x + K * w + K * m * z
                                  : x + K * z + K * m * w;
                rowL[i] = (u8)v;
                rowC[i] = (u8)dflt;
            }
        }
        return true;
    }

    bool leafStair(int t, int xcol, int b) {
        u8* r0 = child[t * NCOL + NU0].data();
        u8* r1 = child[t * NCOL + NU1].data();
        for (int z0 = 0; z0 < m; z0++) {
            int i = xcol + K * z0 + K * m * (((b - z0) % m + m) % m);
            if (r0[i] != d - 1 || r1[i] != d) return false;
        }
        for (int z0 = 0; z0 < m; z0++) {
            int i = xcol + K * z0 + K * m * (((b - z0) % m + m) % m);
            r0[i] = (u8)d; r1[i] = (u8)(d - 1);
        }
        return true;
    }

    bool wildSeam(int t, int xcol, int c, const vector<u8>& table,
                  const array<int, 3>& sigma) {
        set<int> trio(sigma.begin(), sigma.end());
        if (trio != set<int>{NU0, NU1, c}) return false;
        int want[3] = {d - 1, d, d + 1};     // nu0 -> D0, nu1 -> D1, c -> LAST
        int cols[3] = {NU0, NU1, c};
        for (int z0 = 0; z0 < m; z0++)
            for (int z1 = 0; z1 < m; z1++) {
                int i = xcol + K * z0 + K * m * z1;
                for (int j = 0; j < 3; j++)
                    if (child[t * NCOL + cols[j]][i] != want[j]) return false;
            }
        int DIR[3] = {d - 1, d, d + 1};
        for (int z0 = 0; z0 < m; z0++)
            for (int z1 = 0; z1 < m; z1++) {
                int i = xcol + K * z0 + K * m * z1;
                for (int j = 0; j < 3; j++)
                    child[t * NCOL + sigma[j]][i] =
                        (u8)DIR[table[(z0 * m + z1) * 3 + j]];
            }
        return true;
    }

    bool extraLine(int t, int xcol, int xi, int c) {
        if (dirs[t * d + c][xcol] != d - 1) return false;
        u8* rc = child[t * NCOL + c].data();
        u8* r1 = child[t * NCOL + NU1].data();
        for (int z1 = 0; z1 < m; z1++) {
            int i = xcol + K * xi + K * m * z1;
            if (rc[i] != d + 1 || r1[i] != d) return false;
        }
        for (int z1 = 0; z1 < m; z1++) {
            int i = xcol + K * xi + K * m * z1;
            rc[i] = (u8)d; r1[i] = (u8)(d + 1);
        }
        return true;
    }

    // smallest set containing x0 closed under L_{t,c}, L_{t,c2} and their
    // inverses, both colors x-reading throughout; mirrors old_swap_closure
    // (cap checked at BFS-level granularity, like the Python).
    const vector<int>* closure(int t, int c, int c2, int x0) {
        u64 key = (((u64)(t * 16 + c) * 16 + c2) << 32) | (u32)x0;
        if (closureNone.count(key)) return nullptr;
        auto it = closureCache.find(key);
        if (it != closureCache.end()) return &it->second;
        const int cap = 2000;
        vector<char> in(K, 0);
        in[x0] = 1;
        int cnt = 1;
        vector<int> frontier{x0}, nxt;
        bool fail = false;
        auto step = [&](int cc, int x, bool back) -> int {
            int v = dirs[t * d + cc][x];
            if (v >= d - 1) return -1;
            long long pw = powm[v];
            int dig = (int)((x / pw) % m);
            if (!back) return dig < m - 1 ? x + (int)pw : x - (int)((m - 1) * pw);
            return dig > 0 ? x - (int)pw : x + (int)((m - 1) * pw);
        };
        while (!frontier.empty() && !fail) {
            if (cnt > cap) { fail = true; break; }
            nxt.clear();
            for (int x : frontier) {
                for (int cc : {c, c2}) {
                    for (int back = 0; back < 2 && !fail; back++) {
                        int y = step(cc, x, back);
                        if (y < 0) { fail = true; break; }
                        if (!in[y]) { in[y] = 1; cnt++; nxt.push_back(y); }
                    }
                    if (fail) break;
                }
                if (fail) break;
            }
            swap(frontier, nxt);
        }
        if (fail) {
            if (closureNone.size() > 100000) closureNone.clear();
            closureNone.insert(key);
            return nullptr;
        }
        vector<int> X;
        X.reserve(cnt);
        for (int x = 0; x < K; x++) if (in[x]) X.push_back(x);
        if (closureCache.size() > 50000) closureCache.clear();
        return &(closureCache[key] = move(X));
    }

    bool oldOldSwap(int t, int c, int c2, const vector<int>& X) {
        u8* rc = child[t * NCOL + c].data();
        u8* r2 = child[t * NCOL + c2].data();
        const u8* dc = dirs[t * d + c].data();
        const u8* d2 = dirs[t * d + c2].data();
        for (int x : X) {
            int v = dc[x], v2 = d2[x];
            if (v >= d - 1 || v2 >= d - 1) return false;
            for (int z = 0; z < m * m; z++) {
                int i = x + K * z;
                if (rc[i] != v || r2[i] != v2) return false;
            }
        }
        for (int x : X) {
            int v = dc[x], v2 = d2[x];
            for (int z = 0; z < m * m; z++) {
                int i = x + K * z;
                rc[i] = (u8)v2; r2[i] = (u8)v;
            }
        }
        return true;
    }

    // ---- build: apply the plan's pieces in order; returns #skipped -------
    int build(const Plan& p) {
        int skipped = 0;
        for (const Don& dn : p.dons) {
            int leaf = (dn.t != tau_s) ? (dn.axis == 0 ? NU0 : NU1)
                                       : (dn.axis == 0 ? NU1 : NU0);
            const vector<int>* cyc = findOrbit(dn.t, dn.c, dn.start);
            own(dn.t, leaf); own(dn.t, dn.c);
            if (!cyc || !donate(dn.t, dn.c, *cyc, dn.a, dn.axis, leaf))
                skipped++;
        }
        for (const Stair& st : p.stairs) {
            own(st.t, NU0); own(st.t, NU1);
            if (!leafStair(st.t, st.x, st.b)) skipped++;
        }
        for (const Wild& wl : p.wilds) {
            own(wl.t, NU0); own(wl.t, NU1); own(wl.t, wl.c);
            if (wl.lay < 0 || wl.lay >= (int)wilds.size() ||
                !wildSeam(wl.t, wl.x, wl.c, wilds[wl.lay], wl.sigma))
                skipped++;
        }
        for (const Line& el : p.lines) {
            own(el.t, el.c); own(el.t, NU1);
            if (!extraLine(el.t, el.x, el.xi, el.c)) skipped++;
        }
        for (const Oswap& ow : p.oswaps) {
            const vector<int>* X = closure(ow.t, ow.c, ow.c2, ow.x0);
            if (!X) { skipped++; continue; }
            own(ow.t, ow.c); own(ow.t, ow.c2);
            if (!oldOldSwap(ow.t, ow.c, ow.c2, *X)) skipped++;
        }
        return skipped;
    }

    int composeCount(int c) {
        const u8* rows[8];
        for (int t = 0; t < m; t++) rows[t] = child[t * NCOL + c].data();
        const u32* ap[12];
        for (int v = 0; v < NCOL; v++) ap[v] = addt[v].data();
        u32* R = scratchR.data();
        for (int i = 0; i < K2; i++) {
            u32 y = i;
            for (int t = 0; t < m; t++) y = ap[rows[t][y]][y];
            R[i] = y;
        }
        u64* vis = scratchVis.data();
        memset(vis, 0, scratchVis.size() * 8);
        int n = 0;
        for (int i = 0; i < K2; i++) {
            if (vis[i >> 6] & (1ULL << (i & 63))) continue;
            n++;
            u32 x = i;
            while (!(vis[x >> 6] & (1ULL << (x & 63)))) {
                vis[x >> 6] |= 1ULL << (x & 63);
                x = R[x];
            }
        }
        colorsComputed++;
        return n;
    }

    struct Eval { array<int, 12> ncyc, sign; int skipped; };

    Eval evaluate(const Plan& p, bool useCache = true) {
        Eval out{};
        out.skipped = build(p);
        for (int r : touchedList)
            curHash[r] = hashBytes(child[r].data(), K2);
        for (int c = 0; c < NCOL; c++) {
            u64 key = 0x9e3779b97f4a7c15ULL ^ (u64)c;
            for (int t = 0; t < m; t++) {
                key ^= curHash[t * NCOL + c] + 0x9e3779b97f4a7c15ULL +
                       (key << 6) + (key >> 2);
            }
            pair<int, int> hit{-1, 0};
            if (useCache) {
                auto it = retCache[c].find(key);
                if (it != retCache[c].end()) hit = it->second;
            }
            if (hit.first < 0) {
                int n = composeCount(c);
                hit = {n, (K2 - n) % 2 == 0 ? 1 : -1};
                if (retCache[c].size() > 60000) retCache[c].clear();
                retCache[c][key] = hit;
            }
            out.ncyc[c] = hit.first;
            out.sign[c] = hit.second;
        }
        restore();
        evalsDone++;
        return out;
    }

    // ---- v2 (G3): exact parity prediction ---------------------------------
    // sign of one layer map L(i) = addt[row[i]][i], cached by row hash.
    // Returns +1/-1, or 0 if the row is not a bijection (unknown; never the
    // case for template rows / applied pieces, but guarded anyway).
    int layerSignRow(const u8* row, u64 h) {
        auto it = rowSignCache.find(h);
        if (it != rowSignCache.end()) return it->second;
        u64* vis = scratchVis.data();
        memset(vis, 0, scratchVis.size() * 8);
        int s;
        bool bij = true;
        for (int i = 0; i < K2; i++) {
            u32 y = addt[row[i]][i];
            if (vis[y >> 6] & (1ULL << (y & 63))) { bij = false; break; }
            vis[y >> 6] |= 1ULL << (y & 63);
        }
        if (!bij) s = 0;
        else {
            memset(vis, 0, scratchVis.size() * 8);
            int n = 0;
            for (int i = 0; i < K2; i++) {
                if (vis[i >> 6] & (1ULL << (i & 63))) continue;
                n++;
                u32 x = i;
                while (!(vis[x >> 6] & (1ULL << (x & 63)))) {
                    vis[x >> 6] |= 1ULL << (x & 63);
                    x = addt[row[x]][x];
                }
            }
            s = (K2 - n) % 2 == 0 ? 1 : -1;
        }
        layerSignsComputed++;
        if (rowSignCache.size() > 300000) rowSignCache.clear();
        rowSignCache[h] = s;
        return s;
    }

    // v2 (G3): like evaluate(), but after building the child it predicts all
    // nine return signs from cached layer signs; the parity penalty plus the
    // skip penalty is an exact LOWER BOUND on the proposal's energy, so with
    // the (shared) Metropolis draw u the move can be rejected before any
    // compose-count.  Returns false on early reject (engine restored, out
    // partially filled); true after a full evaluation (out complete).
    bool evaluateOrReject(const Plan& p, long long curE, double T, double u,
                          Eval& out) {
        out = Eval{};
        out.skipped = build(p);
        for (int r : touchedList)
            curHash[r] = hashBytes(child[r].data(), K2);
        int pred[12];
        long long Elb = 400LL * out.skipped;
        bool known = true;
        for (int c = 0; c < NCOL; c++) {
            int s = 1;
            for (int t = 0; t < m && s != 0; t++)
                s *= layerSignRow(child[t * NCOL + c].data(),
                                  curHash[t * NCOL + c]);
            pred[c] = s;
            if (s == 0) known = false;
            if (s == 1) Elb += 3000;
        }
        if (g_earlyReject && known && Elb > curE &&
            u >= exp(-(double)(Elb - curE) / max(T, 1e-9))) {
            restore();
            earlyRejects++;
            return false;
        }
        for (int c = 0; c < NCOL; c++) {
            u64 key = 0x9e3779b97f4a7c15ULL ^ (u64)c;
            for (int t = 0; t < m; t++) {
                key ^= curHash[t * NCOL + c] + 0x9e3779b97f4a7c15ULL +
                       (key << 6) + (key >> 2);
            }
            pair<int, int> hit{-1, 0};
            auto it = retCache[c].find(key);
            if (it != retCache[c].end()) hit = it->second;
            if (hit.first < 0) {
                int n = composeCount(c);
                hit = {n, (K2 - n) % 2 == 0 ? 1 : -1};
                if (retCache[c].size() > 60000) retCache[c].clear();
                retCache[c][key] = hit;
            }
            out.ncyc[c] = hit.first;
            out.sign[c] = hit.second;
            if (pred[c] != 0 && pred[c] != hit.second) signMismatch++;
        }
        restore();
        evalsDone++;
        return true;
    }
};

// --------------------------------------------------------------- energy
long long energyOf(const Engine& eng, const Engine::Eval& ev, int lw) {
    long long E = 0;
    for (int c = 0; c < eng.d; c++) E += ev.ncyc[c] - 1;
    for (int c = eng.d; c < eng.NCOL; c++) E += (long long)lw * (ev.ncyc[c] - 1);
    E += 400LL * ev.skipped;
    for (int c = 0; c < eng.NCOL; c++) if (ev.sign[c] == 1) E += 3000;
    return E;
}

// --------------------------------------------------------------- JSON i/o
Plan planFromJV(const JV& w) {
    Plan p;
    if (auto* a = w.get("donations"))
        for (auto& e : a->arr)
            p.dons.push_back({(int)e.arr[0].i(), (int)e.arr[1].i(),
                              (int)e.arr[2].i(), (int)e.arr[3].i(),
                              (int)e.arr[4].i()});
    if (auto* a = w.get("stairs"))
        for (auto& e : a->arr)
            p.stairs.push_back({(int)e.arr[0].i(), (int)e.arr[1].i(),
                                (int)e.arr[2].i()});
    if (auto* a = w.get("wilds"))
        for (auto& e : a->arr)
            p.wilds.push_back({(int)e.arr[0].i(), (int)e.arr[1].i(),
                               (int)e.arr[2].i(), (int)e.arr[3].i(),
                               {(int)e.arr[4].arr[0].i(),
                                (int)e.arr[4].arr[1].i(),
                                (int)e.arr[4].arr[2].i()}});
    if (auto* a = w.get("lines"))
        for (auto& e : a->arr)
            p.lines.push_back({(int)e.arr[0].i(), (int)e.arr[1].i(),
                               (int)e.arr[2].i(), (int)e.arr[3].i()});
    if (auto* a = w.get("oswaps"))
        for (auto& e : a->arr)
            p.oswaps.push_back({(int)e.arr[0].i(), (int)e.arr[1].i(),
                                (int)e.arr[2].i(), (int)e.arr[3].i()});
    return p;
}

string planToJson(const Engine& eng, const Plan& p, long long E,
                  const array<int, 12>* ncyc) {
    ostringstream o;
    o << "{\n \"m\": " << eng.m << ",\n \"tau_s\": " << eng.tau_s << ",\n";
    o << " \"donations\": [";
    for (size_t i = 0; i < p.dons.size(); i++) {
        const Don& d = p.dons[i];
        o << (i ? ", " : "") << "[" << d.axis << ", " << d.t << ", " << d.c
          << ", " << d.start << ", " << d.a << "]";
    }
    o << "],\n \"stairs\": [";
    for (size_t i = 0; i < p.stairs.size(); i++)
        o << (i ? ", " : "") << "[" << p.stairs[i].t << ", " << p.stairs[i].x
          << ", " << p.stairs[i].b << "]";
    o << "],\n \"wilds\": [";
    for (size_t i = 0; i < p.wilds.size(); i++) {
        const Wild& w = p.wilds[i];
        o << (i ? ", " : "") << "[" << w.t << ", " << w.x << ", " << w.c
          << ", " << w.lay << ", [" << w.sigma[0] << ", " << w.sigma[1]
          << ", " << w.sigma[2] << "]]";
    }
    o << "],\n \"lines\": [";
    for (size_t i = 0; i < p.lines.size(); i++)
        o << (i ? ", " : "") << "[" << p.lines[i].t << ", " << p.lines[i].x
          << ", " << p.lines[i].xi << ", " << p.lines[i].c << "]";
    o << "],\n \"oswaps\": [";
    for (size_t i = 0; i < p.oswaps.size(); i++)
        o << (i ? ", " : "") << "[" << p.oswaps[i].t << ", " << p.oswaps[i].c
          << ", " << p.oswaps[i].c2 << ", " << p.oswaps[i].x0 << "]";
    o << "],\n \"cross0\": {";
    for (int c = 0; c < eng.d; c++)
        o << (c ? ", " : "") << "\"" << c << "\": [" << eng.cross0[c][0]
          << ", " << eng.cross0[c][1] << "]";
    o << "},\n \"cross1\": {";
    for (int c = 0; c < eng.d; c++)
        o << (c ? ", " : "") << "\"" << c << "\": [" << eng.cross1[c][0]
          << ", " << eng.cross1[c][1] << ", " << eng.cross1[c][2] << "]";
    o << "}";
    if (ncyc) {
        o << ",\n \"E\": " << E << ",\n \"ncyc\": [";
        for (int c = 0; c < eng.NCOL; c++)
            o << (c ? ", " : "") << (*ncyc)[c];
        o << "]";
    }
    o << "\n}\n";
    return o.str();
}

void atomicWrite(const string& path, const string& content) {
    string tmp = path + ".tmp" + to_string(getpid());
    ofstream f(tmp, ios::binary);
    f << content;
    f.close();
    rename(tmp.c_str(), path.c_str());
}

// --------------------------------------------------------------- RNG
struct RNG {
    mt19937_64 g;
    RNG(u64 s) : g(s) {}
    double rnd() { return uniform_real_distribution<double>(0.0, 1.0)(g); }
    int rr(int n) { return (int)(g() % (u64)n); }
    int rr(int lo, int hi) { return lo + rr(hi - lo); }   // [lo, hi)
    template <class T>
    const T& choice(const vector<T>& v) { return v[rr((int)v.size())]; }
    template <class T>
    void shuf(vector<T>& v) {
        for (int i = (int)v.size() - 1; i > 0; i--) swap(v[i], v[rr(i + 1)]);
    }
};

// --------------------------------------------------------------- make_plan
struct PlanCtx {
    Plan plan;
    map<pair<int, int>, vector<int>> zeroCols;    // (t,c) -> columns
    vector<pair<int, int>> zeroKeys;              // insertion order
    vector<set<int>> donatedCols;                 // per layer
};

// faithful port of make_plan (random offsets, full coverage + connectivity
// patching, parity-pair stairs, one wild seam + compensating line)
bool makePlan(Engine& eng, RNG& rng, PlanCtx& ctx, int n_blocks = 2) {
    int d = eng.d, m = eng.m, K = eng.K, tau_s = eng.tau_s;
    ctx = PlanCtx();
    ctx.donatedCols.assign(m, {});
    set<pair<int, int>> usedPairs;
    vector<vector<set<int>>> bad(2, vector<set<int>>(m));
    for (int c = 0; c < d; c++) bad[0][eng.cross0[c][0]].insert(eng.cross0[c][1]);
    for (int c = 0; c < d; c++) bad[1][eng.cross1[c][0]].insert(eng.cross1[c][1]);
    for (int leaf = 0; leaf < 2; leaf++) {
        auto axisAt = [&](int t) { return t != tau_s ? leaf : 1 - leaf; };
        vector<int> lays(m);
        iota(lays.begin(), lays.end(), 0);
        rng.shuf(lays);
        auto okOrbs = [&](int t, int c) {
            vector<const vector<int>*> out;
            const set<int>& bb = bad[axisAt(t)][t];
            for (const auto& cy : eng.orbits[t * d + c]) {
                bool clash = false;
                for (int x : cy) if (bb.count(x)) { clash = true; break; }
                if (!clash) out.push_back(&cy);
            }
            return out;
        };
        vector<pair<int, int>> blocks;
        for (int bi = 0; bi < n_blocks; bi++) {
            int t = lays[bi];
            vector<int> cands;
            for (int c = 0; c < d; c++)
                if (!usedPairs.count({t, c})) cands.push_back(c);
            if (cands.empty()) return false;
            blocks.push_back({t, rng.choice(cands)});
        }
        set<pair<int, int>> blockSet(blocks.begin(), blocks.end());
        vector<tuple<int, int, const vector<int>*>> chosen;
        for (auto [t, c] : blocks)
            for (auto* cy : okOrbs(t, c)) chosen.push_back({t, c, cy});
        // union-find connectivity over the K columns
        vector<int> parent(K);
        iota(parent.begin(), parent.end(), 0);
        function<int(int)> find = [&](int a) {
            while (parent[a] != a) { parent[a] = parent[parent[a]]; a = parent[a]; }
            return a;
        };
        vector<char> deg(K, 0);
        int covered = 0;
        auto addOrbit = [&](const vector<int>& cy) {
            for (size_t j = 0; j < cy.size(); j++) {
                int x = cy[j];
                if (!deg[x]) { deg[x] = 1; covered++; }
                int y = cy[(j + 1) % cy.size()];
                int ra = find(x), rb = find(y);
                if (ra != rb) parent[ra] = rb;
            }
        };
        for (auto& [t, c, cy] : chosen) { (void)t; (void)c; addOrbit(*cy); }
        vector<pair<int, int>> pool;
        for (int t : lays)
            for (int c = 0; c < d; c++)
                if (!blockSet.count({t, c}) && !usedPairs.count({t, c}))
                    pool.push_back({t, c});
        rng.shuf(pool);
        vector<pair<int, int>> patchPairs;
        auto ncompAll = [&]() {
            set<int> roots;
            for (int x = 0; x < K; x++) roots.insert(find(x));
            return (int)roots.size();
        };
        for (auto [t, c] : pool) {
            if (covered == K && ncompAll() == 1) break;
            for (auto* cy : okOrbs(t, c)) {
                bool helps = false;
                for (int x : *cy) if (!deg[x]) { helps = true; break; }
                if (!helps) {
                    set<int> roots;
                    for (int x : *cy) roots.insert(find(x));
                    helps = roots.size() > 1;
                }
                if (helps) {
                    addOrbit(*cy);
                    chosen.push_back({t, c, cy});
                    patchPairs.push_back({t, c});
                }
            }
        }
        if (covered != K || ncompAll() != 1) return false;
        for (auto& b : blocks) usedPairs.insert(b);
        for (auto& b : patchPairs) usedPairs.insert(b);
        // conflict-aware offsets within (leaf, layer)
        map<int, set<pair<int, int>>> cellmap;
        for (auto& [t, c, cyp] : chosen) {
            const vector<int>& cyc = *cyp;
            auto& usedCells = cellmap[t];
            int L = (int)cyc.size();
            int q = m / __gcd(L, m);
            vector<int> offs(m);
            iota(offs.begin(), offs.end(), 0);
            rng.shuf(offs);
            for (int a : offs) {
                bool clash = false;
                vector<pair<int, int>> cells(q * L);
                for (int j = 0; j < q * L; j++) {
                    cells[j] = {cyc[j % L], ((a - j) % m + m) % m};
                    if (usedCells.count(cells[j])) { clash = true; break; }
                }
                if (!clash) {
                    usedCells.insert(cells.begin(), cells.end());
                    ctx.plan.dons.push_back({axisAt(t), t, c, cyc[0], a});
                    ctx.donatedCols[t].insert(cyc.begin(), cyc.end());
                    break;
                }
            }
        }
    }
    // parity-pair stairs on donation-free columns
    for (int s = 0; s < 4; s++) {
        for (int tr = 0; tr < 40; tr++) {
            int t = rng.rr(m), xcol = rng.rr(K);
            if (!ctx.donatedCols[t].count(xcol)) {
                ctx.plan.stairs.push_back({t, xcol, rng.rr(m)});
                break;
            }
        }
    }
    // wild seam + compensating line on zero-read columns
    for (int t = 0; t < m; t++) {
        if (t == tau_s) continue;
        for (int c = 0; c < d; c++) {
            vector<int> cols;
            for (int x = 0; x < K; x++)
                if (eng.dirs[t * d + c][x] == d - 1 &&
                    !ctx.donatedCols[t].count(x))
                    cols.push_back(x);
            if ((int)cols.size() >= 2) {
                ctx.zeroCols[{t, c}] = move(cols);
                ctx.zeroKeys.push_back({t, c});
            }
        }
    }
    if (ctx.zeroKeys.empty()) return false;
    auto [t, c] = rng.choice(ctx.zeroKeys);
    const vector<int>& zcols = ctx.zeroCols[{t, c}];
    int xw = rng.choice(zcols);
    int lay = rng.rr((int)eng.wilds.size());
    vector<int> sigma{eng.NU0, eng.NU1, c};
    rng.shuf(sigma);
    ctx.plan.wilds.push_back({t, xw, c, lay, {sigma[0], sigma[1], sigma[2]}});
    vector<int> lcols;
    for (int x : zcols) if (x != xw) lcols.push_back(x);
    ctx.plan.lines.push_back({t, rng.choice(lcols), rng.rr(m), c});
    return true;
}

// recompute zeroCols for a resumed plan (Python leaves them empty on resume;
// recomputing gives the wild/line moves their full column supply)
void rebuildZeroCols(Engine& eng, PlanCtx& ctx) {
    int d = eng.d, m = eng.m, K = eng.K;
    ctx.donatedCols.assign(m, {});
    for (const Don& dn : ctx.plan.dons) {
        const vector<int>* cy = eng.findOrbit(dn.t, dn.c, dn.start);
        if (cy) ctx.donatedCols[dn.t].insert(cy->begin(), cy->end());
    }
    ctx.zeroCols.clear();
    ctx.zeroKeys.clear();
    for (int t = 0; t < m; t++) {
        if (t == eng.tau_s) continue;
        for (int c = 0; c < d; c++) {
            vector<int> cols;
            for (int x = 0; x < K; x++)
                if (eng.dirs[t * d + c][x] == d - 1 &&
                    !ctx.donatedCols[t].count(x))
                    cols.push_back(x);
            if ((int)cols.size() >= 2) {
                ctx.zeroCols[{t, c}] = move(cols);
                ctx.zeroKeys.push_back({t, c});
            }
        }
    }
}

// ------------------------------------------------------- v2 (G2) repair pass
// Move POST-condition repair (design-ledger guidance (ii): donor coverage
// must hold at gated granularity; enforce it structurally instead of letting
// the +400 skip / leaf-cycle plateau discover it).
//  pass 1: donation cell conflicts (exactly the donate() precondition wrt
//          other donations) -> re-offset the later donation to a free
//          storey, else drop it; dead orbit references dropped.
//  pass 2: stairs on donated columns of their layer (always skipped by
//          leafStair) -> moved to a donation-free column; exact duplicate
//          stairs dropped.
//  pass 3: gated keep-coverage: for every donor color c and donated column
//          x, every (z0,z1) storey must keep >= 1 movable layer t with z0
//          ungated (axis-0 dons) and z1 ungated (axis-1 dons); violations
//          repaired by dropping one offending donation (capped per call).
void repairPlan(Engine& eng, RNG& rng, Plan& p) {
    int m = eng.m, d = eng.d, K = eng.K, K2 = eng.K2, NCOL = eng.NCOL;
    // ---- pass 1: conflict-aware re-offsetting (flat claim bitmap) ----
    {
        u64* claim = eng.repClaim.data();
        memset(claim, 0, eng.repClaim.size() * 8);
        auto claimed = [&](int t, int row, int i) {
            size_t b = (size_t)(t * NCOL + row) * K2 + i;
            return (claim[b >> 6] >> (b & 63)) & 1;
        };
        auto setClaim = [&](int t, int row, int i) {
            size_t b = (size_t)(t * NCOL + row) * K2 + i;
            claim[b >> 6] |= 1ULL << (b & 63);
        };
        vector<int> drop;
        for (int j = 0; j < (int)p.dons.size(); j++) {
            Don& dn = p.dons[j];
            const vector<int>* cyp = eng.findOrbit(dn.t, dn.c, dn.start);
            if (!cyp) { drop.push_back(j); continue; }
            const vector<int>& cy = *cyp;
            int leaf = (dn.t != eng.tau_s) ? (dn.axis == 0 ? eng.NU0 : eng.NU1)
                                           : (dn.axis == 0 ? eng.NU1 : eng.NU0);
            int L = (int)cy.size(), q = m / __gcd(L, m), n = q * L;
            bool placed = false;
            for (int s = 0; s < m && !placed; s++) {
                int a = (dn.a + s) % m;
                bool clash = false;
                for (int jj = 0; jj < n && !clash; jj++) {
                    int x = cy[jj % L], w = ((a - jj) % m + m) % m;
                    for (int z = 0; z < m; z++) {
                        int i = dn.axis == 0 ? x + K * w + K * m * z
                                             : x + K * z + K * m * w;
                        if (claimed(dn.t, leaf, i) || claimed(dn.t, dn.c, i)) {
                            clash = true;
                            break;
                        }
                    }
                }
                if (!clash) {
                    dn.a = a;
                    for (int jj = 0; jj < n; jj++) {
                        int x = cy[jj % L], w = ((a - jj) % m + m) % m;
                        for (int z = 0; z < m; z++) {
                            int i = dn.axis == 0 ? x + K * w + K * m * z
                                                 : x + K * z + K * m * w;
                            setClaim(dn.t, leaf, i);
                            setClaim(dn.t, dn.c, i);
                        }
                    }
                    placed = true;
                }
            }
            if (!placed) drop.push_back(j);
        }
        for (int k = (int)drop.size() - 1; k >= 0; k--)
            p.dons.erase(p.dons.begin() + drop[k]);
    }
    // ---- pass 2: stairs off donated columns; duplicate stairs dropped ----
    {
        u8* donCol = eng.repDonCol.data();
        memset(donCol, 0, (size_t)m * K);
        for (const Don& dn : p.dons) {
            const vector<int>* cy = eng.findOrbit(dn.t, dn.c, dn.start);
            if (cy) for (int x : *cy) donCol[dn.t * K + x] = 1;
        }
        set<tuple<int, int, int>> seen;
        vector<int> drop;
        for (int j = 0; j < (int)p.stairs.size(); j++) {
            Stair& st = p.stairs[j];
            if (st.t == eng.tau_s || donCol[st.t * K + st.x]) {
                bool moved = false;
                for (int tr = 0; tr < 40 && !moved; tr++) {
                    int t = rng.rr(m), x = rng.rr(K);
                    if (t != eng.tau_s && !donCol[t * K + x]) {
                        st = {t, x, rng.rr(m)};
                        moved = true;
                    }
                }
                if (!moved) { drop.push_back(j); continue; }
            }
            if (!seen.insert({st.t, st.x, st.b}).second) drop.push_back(j);
        }
        for (int k = (int)drop.size() - 1; k >= 0; k--)
            p.stairs.erase(p.stairs.begin() + drop[k]);
    }
    // ---- pass 3: gated donor keep-coverage (flat storey-mask arrays) ----
    for (int round = 0; round < 3; round++) {
        u8* g0 = eng.repG0.data();
        u8* g1 = eng.repG1.data();
        u8* cxSeen = eng.repCxSeen.data();
        memset(g0, 0, (size_t)m * d * K);
        memset(g1, 0, (size_t)m * d * K);
        memset(cxSeen, 0, (size_t)d * K);
        vector<int> cxList;                      // c*K + x, deduped
        for (int j = 0; j < (int)p.dons.size(); j++) {
            const Don& dn = p.dons[j];
            const vector<int>* cyp = eng.findOrbit(dn.t, dn.c, dn.start);
            if (!cyp) continue;
            int L = (int)cyp->size(), q = m / __gcd(L, m), n = q * L;
            u8* g = dn.axis == 0 ? g0 : g1;
            for (int jj = 0; jj < n; jj++) {
                int x = (*cyp)[jj % L], w = ((dn.a - jj) % m + m) % m;
                g[(dn.t * d + dn.c) * K + x] |= (u8)(1 << w);
                int cx = dn.c * K + x;
                if (!cxSeen[cx]) { cxSeen[cx] = 1; cxList.push_back(cx); }
            }
        }
        // violation scan.  NOTE: a static per-(z0,z1)-storey test is TOO
        // STRICT -- the fiber coordinates evolve through the layer word
        // (D0/D1 steps between layers), so a storey with no statically
        // ungated slot can still be traversed; the clean E(lw1)=6 frontier
        // plan violates the static test on 3 columns while all old-color
        // words are (near-)single.  Enforce only the SAFE necessary
        // condition: column x is dead for donor c iff EVERY movable layer
        // carries a FULL gate mask on some axis (then no fiber state can
        // ever take the x-read there).
        int vc = -1, vx = -1, vz0 = -1, vz1 = -1;
        u8 full = (u8)((1 << m) - 1);
        for (int cx : cxList) {
            if (vc >= 0) break;
            int c = cx / K, x = cx % K;
            u8 mv = eng.movMask[cx];
            bool alive = false;
            for (int t = 0; t < m; t++)
                if ((mv >> t & 1) && g0[(t * d + c) * K + x] != full &&
                    g1[(t * d + c) * K + x] != full) {
                    alive = true;
                    break;
                }
            if (!alive) {
                // pick any fully-gated movable layer's axis/storey to blame
                for (int t = 0; t < m && vc < 0; t++) {
                    if (!(mv >> t & 1)) continue;
                    if (g0[(t * d + c) * K + x] == full) {
                        vc = c; vx = x; vz0 = 0; vz1 = -1;
                    } else if (g1[(t * d + c) * K + x] == full) {
                        vc = c; vx = x; vz0 = -1; vz1 = 0;
                    }
                }
            }
        }
        if (vc < 0) break;
        // drop one donation gating the dead column at a movable layer
        (void)vz0; (void)vz1;
        vector<int> cand;
        for (int j = 0; j < (int)p.dons.size(); j++) {
            const Don& dn = p.dons[j];
            if (dn.c != vc) continue;
            if (!(eng.movMask[vc * K + vx] >> dn.t & 1)) continue;
            const vector<int>* cyp = eng.findOrbit(dn.t, dn.c, dn.start);
            if (!cyp) continue;
            for (int x : *cyp)
                if (x == vx) { cand.push_back(j); break; }
        }
        if (cand.empty()) break;
        p.dons.erase(p.dons.begin() + cand[rng.rr((int)cand.size())]);
    }
}

// ----------------------------------------------------- v2 (M) leaf-merge move
// Build the current plan, label the chosen leaf color's return cycles, and
// look for leaf staircases (t, x, b), t != tau_s, whose m anti-diagonal
// cells (x, z0, b - z0) pass through >= 2 DISTINCT return cycles of the leaf
// (cell i at stage t lies on the cycle of its forward image through layers
// t..m-1): a gated boundary swap that can merge them.  The stair's
// leafStair() precondition is checked on the built child, so the proposal is
// never skipped.  ONE stair flips the sign of BOTH leaf returns (odd
// deviation on both; the reason v1 only ever adds stairs in pairs), so the
// move collects up to TWO boundary stairs; with only one found the caller
// must pair it with a compensating stair elsewhere or the proposal is
// parity-dead (observed: 0/726 accepted before this fix).  Returns the
// number of boundary stairs found (0..2) in `out`.
int proposeLeafMerge(Engine& eng, RNG& rng, const Plan& plan, int leaf,
                     array<Stair, 2>& out) {
    int m = eng.m, d = eng.d, K = eng.K, K2 = eng.K2;
    eng.build(plan);
    static vector<u32> R;
    static vector<int> lab;
    R.resize(K2);
    lab.assign(K2, -1);
    const u8* rows[8];
    for (int t = 0; t < m; t++)
        rows[t] = eng.child[t * eng.NCOL + leaf].data();
    for (int i = 0; i < K2; i++) {
        u32 y = i;
        for (int t = 0; t < m; t++) y = eng.addt[rows[t][y]][y];
        R[i] = y;
    }
    int nc = 0;
    for (int i = 0; i < K2; i++) {
        if (lab[i] >= 0) continue;
        u32 x = i;
        while (lab[x] < 0) { lab[x] = nc; x = R[x]; }
        nc++;
    }
    int found = 0;
    if (nc >= 2) {
        // giant = most frequent label; candidate columns = the x-support of
        // the PARASITE cycles (every stair there straddles parasite+giant
        // with high probability; uniform-x scans almost never hit them)
        vector<int> cnt(nc, 0);
        for (int i = 0; i < K2; i++) cnt[lab[i]]++;
        int gLab = (int)(max_element(cnt.begin(), cnt.end()) - cnt.begin());
        vector<int> pcols;
        {
            static vector<u8> mark;
            mark.assign(K, 0);
            for (int i = 0; i < K2; i++)
                if (lab[i] != gLab && !mark[i % K]) {
                    mark[i % K] = 1;
                    pcols.push_back(i % K);
                }
        }
        rng.shuf(pcols);
        vector<int> lays;
        for (int t = 0; t < m; t++) if (t != eng.tau_s) lays.push_back(t);
        for (int x : pcols) {
            if (found >= 2) break;
            rng.shuf(lays);
            for (int t : lays) {
                if (found >= 2) break;
                const u8* r0 = eng.child[t * eng.NCOL + eng.NU0].data();
                const u8* r1 = eng.child[t * eng.NCOL + eng.NU1].data();
                int b0 = rng.rr(m);
                for (int db = 0; db < m && found < 2; db++) {
                    int b = (b0 + db) % m;
                    if (found == 1 && out[0].t == t && out[0].x == x)
                        continue;
                    bool ok = true, multi = false;
                    int seenLab = -1;
                    for (int z0 = 0; z0 < m; z0++) {
                        int i = x + K * z0 +
                                K * m * (((b - z0) % m + m) % m);
                        if (r0[i] != d - 1 || r1[i] != d) {
                            ok = false;
                            break;
                        }
                        u32 y = (u32)i;
                        for (int tt = t; tt < m; tt++)
                            y = eng.addt[eng.child[tt * eng.NCOL + leaf][y]][y];
                        if (seenLab < 0) seenLab = lab[y];
                        else if (lab[y] != seenLab) multi = true;
                    }
                    if (ok && multi) out[found++] = {t, x, b};
                }
            }
        }
    }
    eng.restore();
    return found;
}

// --------------------------------------------------------------- mutate
// faithful port of mutate() (same move catalog and probabilities)
void mutatePlan(Engine& eng, RNG& rng, const PlanCtx& ctx, const Plan& plan,
                int worst, Plan& p2) {
    p2 = plan;
    int d = eng.d, m = eng.m, K = eng.K;
    double r = rng.rnd();
    if (r < 0.14) {
        if (!p2.oswaps.empty() && rng.rnd() < 0.4) {
            p2.oswaps.erase(p2.oswaps.begin() + rng.rr((int)p2.oswaps.size()));
        } else {
            int cw = (worst >= 0 && worst < d) ? worst : rng.rr(d);
            vector<int> others;
            for (int c = 0; c < d; c++) if (c != cw) others.push_back(c);
            int c2 = rng.choice(others);
            p2.oswaps.push_back({rng.rr(m), cw, c2, rng.rr(K)});
        }
    } else if (r < 0.62 && !p2.dons.empty()) {
        vector<int> idx((int)p2.dons.size());
        iota(idx.begin(), idx.end(), 0);
        if (rng.rnd() < 0.6) {
            vector<int> cand;
            for (int j = 0; j < (int)p2.dons.size(); j++) {
                const Don& dn = p2.dons[j];
                bool sel = dn.c == worst ||
                           (worst >= d && ((dn.axis == worst - d) !=
                                           (dn.t == eng.tau_s)));
                if (sel) cand.push_back(j);
            }
            if (!cand.empty()) idx = cand;
        }
        int j = rng.choice(idx);
        Don dn = p2.dons[j];
        double u = rng.rnd();
        if (u < 0.70) {
            p2.dons[j].a = (dn.a + rng.rr(1, m)) % m;
        } else if (u < 0.78) {
            int reps = rng.rr(2, 6);
            for (int k = 0; k < reps; k++) {
                int jj = rng.choice(idx);
                p2.dons[jj].a = (p2.dons[jj].a + rng.rr(1, m)) % m;
            }
        } else if (u < 0.86) {
            p2.dons.push_back({dn.axis, dn.t, dn.c, dn.start,
                               (dn.a + rng.rr(1, m)) % m});
        } else if (u < 0.93) {
            int victim = j;
            if (g_purity && rng.rnd() < 0.6) {
                // (G1) prefer deleting a donation whose color is in the
                // minority on its leaf (purify the leaf word)
                int cnt[2][16] = {{0}};
                for (const Don& dd : p2.dons) {
                    int lf = (dd.t != eng.tau_s) ? dd.axis : 1 - dd.axis;
                    cnt[lf][dd.c]++;
                }
                int bestScore = INT_MAX;
                for (int jj : idx) {
                    const Don& dd = p2.dons[jj];
                    int lf = (dd.t != eng.tau_s) ? dd.axis : 1 - dd.axis;
                    if (cnt[lf][dd.c] < bestScore) {
                        bestScore = cnt[lf][dd.c];
                        victim = jj;
                    }
                }
            }
            p2.dons.erase(p2.dons.begin() + victim);
        } else {
            int leaf = rng.rr(2);
            int t2 = rng.rr(m);
            int ax2 = t2 != eng.tau_s ? leaf : 1 - leaf;
            int c2 = rng.rr(d);
            if (g_purity && rng.rnd() < 0.7) {
                // (G1) bias the new donation toward the target leaf's
                // dominant donated color (leaf words must stay near
                // single-color words: ledger T2b)
                int cnt[16] = {0};
                for (const Don& dd : p2.dons) {
                    int lf = (dd.t != eng.tau_s) ? dd.axis : 1 - dd.axis;
                    if (lf == leaf) cnt[dd.c]++;
                }
                int best = -1;
                for (int c = 0; c < d; c++)
                    if (best < 0 || cnt[c] > cnt[best]) best = c;
                if (best >= 0 && cnt[best] > 0) c2 = best;
            }
            const auto& cycs = eng.orbits[t2 * d + c2];
            if (!cycs.empty()) {
                const auto& cy = cycs[rng.rr((int)cycs.size())];
                p2.dons.push_back({ax2, t2, c2, cy[0], rng.rr(m)});
            }
        }
    } else if (r < 0.74) {
        vector<int> lays;
        for (int t = 0; t < m; t++) if (t != eng.tau_s) lays.push_back(t);
        double u = rng.rnd();
        if (u < 0.6 && !p2.stairs.empty()) {
            int j = rng.rr((int)p2.stairs.size());
            p2.stairs[j] = {rng.choice(lays), rng.rr(K), rng.rr(m)};
        } else if (u < 0.8 && (int)p2.stairs.size() >= 2) {
            p2.stairs.erase(p2.stairs.begin() + rng.rr((int)p2.stairs.size()));
            p2.stairs.erase(p2.stairs.begin() + rng.rr((int)p2.stairs.size()));
        } else {
            for (int k = 0; k < 2; k++)
                p2.stairs.push_back({rng.choice(lays), rng.rr(K), rng.rr(m)});
        }
    } else if (r < 0.88 && !p2.wilds.empty()) {
        int j = rng.rr((int)p2.wilds.size());
        Wild w = p2.wilds[j];
        double u = rng.rnd();
        if (u < 0.35) {
            w.lay = rng.rr((int)eng.wilds.size());
        } else if (u < 0.7) {
            vector<int> sg(w.sigma.begin(), w.sigma.end());
            rng.shuf(sg);
            w.sigma = {sg[0], sg[1], sg[2]};
        } else {
            auto it = ctx.zeroCols.find({w.t, w.c});
            if (it != ctx.zeroCols.end() && !it->second.empty())
                w.x = rng.choice(it->second);
        }
        p2.wilds[j] = w;
    } else if (!p2.lines.empty()) {
        int j = rng.rr((int)p2.lines.size());
        Line el = p2.lines[j];
        vector<int> fallback;
        const vector<int>* cols = nullptr;
        auto it = ctx.zeroCols.find({el.t, el.c});
        if (it != ctx.zeroCols.end() && !it->second.empty()) {
            cols = &it->second;
        } else {
            for (int x = 0; x < K; x++)
                if (eng.dirs[el.t * d + el.c][x] == d - 1)
                    fallback.push_back(x);
            cols = &fallback;
        }
        if (!cols->empty())
            p2.lines[j] = {el.t, (*cols)[rng.rr((int)cols->size())],
                           rng.rr(m), el.c};
    }
}

// --------------------------------------------------------------- modes
string fmtVec(const array<int, 12>& v, int n) {
    ostringstream o;
    o << "[";
    for (int i = 0; i < n; i++) o << (i ? ", " : "") << v[i];
    o << "]";
    return o.str();
}

int checkPlans(Engine& eng, const string& basePath,
               const vector<string>& files) {
    for (const string& f : files) {
        string raw = slurp(f);
        JParser jp(raw);
        JV w = jp.parse();
        int mm = (int)w.get("m")->i();
        if (eng.m != mm) {
            fprintf(stderr, "plan %s has m=%d, base %s has m=%d\n",
                    f.c_str(), mm, basePath.c_str(), eng.m);
            return 1;
        }
        // crossings from the plan file (matches rebuild_from_witness)
        for (int c = 0; c < eng.d; c++) {
            const JV* e0 = w.get("cross0")->get(to_string(c));
            const JV* e1 = w.get("cross1")->get(to_string(c));
            eng.cross0[c] = {(int)e0->arr[0].i(), (int)e0->arr[1].i()};
            eng.cross1[c] = {(int)e1->arr[0].i(), (int)e1->arr[1].i(),
                             (int)e1->arr[2].i()};
        }
        eng.buildTemplate((int)w.get("tau_s")->i());
        Plan p = planFromJV(w);
        Engine::Eval ev = eng.evaluate(p, false);
        long long E1 = energyOf(eng, ev, 1);
        printf("CHECK %s tau_s=%d E(lw1)=%lld ncyc=%s signs=%s skipped=%d\n",
               f.c_str(), eng.tau_s, E1, fmtVec(ev.ncyc, eng.NCOL).c_str(),
               fmtVec(ev.sign, eng.NCOL).c_str(), ev.skipped);
        fflush(stdout);
    }
    return 0;
}

int annealMain(Engine& eng, u64 seed, long long iters, int restarts,
               int leafWeight, int forceTau, const string& tag,
               const string& resumeFile) {
    RNG rng(seed);
    string bestPath = "growth_conjugate_best_m" + to_string(eng.m) + "_cpp_" +
                      (tag.empty() ? ("s" + to_string(seed)) : tag) + ".json";
    string hitPath = "growth_conjugate_hit_m" + to_string(eng.m) + ".json";
    printf("=== fast seam anneal (7,%d): seed=%llu iters=%lld restarts=%d "
           "leaf_weight=%d tag=%s ===\n",
           eng.m, (unsigned long long)seed, iters, restarts, leafWeight,
           tag.c_str());
    fflush(stdout);
    auto t0wall = chrono::steady_clock::now();
    long long globalBestE = LLONG_MAX;
    bool haveResume = !resumeFile.empty();
    JV resume;
    if (haveResume) {
        string raw = slurp(resumeFile);
        JParser jp(raw);
        resume = jp.parse();
        if ((int)resume.get("m")->i() != eng.m) {
            fprintf(stderr, "resume m mismatch\n");
            return 1;
        }
    }
    for (int rs = 0; rs < restarts; rs++) {
        int tau;
        PlanCtx ctx;
        if (haveResume) {
            tau = (int)resume.get("tau_s")->i();
            eng.buildTemplate(tau);
            ctx.plan = planFromJV(resume);
            rebuildZeroCols(eng, ctx);
            haveResume = false;
        } else {
            tau = forceTau >= 0 ? forceTau : rng.rr(eng.m);
            eng.buildTemplate(tau);
            bool ok = false;
            for (int tries = 0; tries < 60 && !ok; tries++)
                ok = makePlan(eng, rng, ctx);
            if (!ok) {
                printf("[restart %d] no connected plan\n", rs);
                continue;
            }
        }
        Plan plan = ctx.plan;
        Engine::Eval ev = eng.evaluate(plan);
        long long E = energyOf(eng, ev, leafWeight);
        int maxn = *max_element(ev.ncyc.begin(), ev.ncyc.begin() + eng.NCOL);
        double T0 = max(4, min(300, maxn)), T1 = 0.6;
        printf("[restart %d] tau_s=%d E=%lld ncyc=%s skipped=%d\n", rs, tau,
               E, fmtVec(ev.ncyc, eng.NCOL).c_str(), ev.skipped);
        fflush(stdout);
        Plan bestPlan = plan;
        Engine::Eval bestEv = ev;
        long long bestE = E;
        long long stall = 0;
        long long stallLimit = max(30000LL, iters / 8);
        long long mergeProps = 0, mergeAccs = 0;
        Plan p2;
        for (long long it = 0; it < iters; it++) {
            double T = T0 * pow(T1 / T0, (double)it / max(1LL, iters - 1));
            int worst = 0;
            for (int c = 1; c < eng.NCOL; c++)
                if (ev.ncyc[c] > ev.ncyc[worst]) worst = c;
            // (M) targeted leaf-merge proposal (always a stair PAIR: one
            // stair flips both leaf signs, so a lone boundary stair is
            // parity-dead; pair with a second boundary stair when found,
            // else with a compensating random stair)
            bool merged = false;
            if (g_mergeProb > 0 && rng.rnd() < g_mergeProb) {
                int leaf = ev.ncyc[eng.NU0] >= ev.ncyc[eng.NU1] ? eng.NU0
                                                                : eng.NU1;
                array<Stair, 2> st{};
                int nf = ev.ncyc[leaf] > 1
                             ? proposeLeafMerge(eng, rng, plan, leaf, st)
                             : 0;
                if (nf > 0) {
                    p2 = plan;
                    if (nf > 1) {
                        p2.stairs.push_back(st[0]);
                        p2.stairs.push_back(st[1]);
                    } else if (!p2.stairs.empty() && rng.rnd() < 0.5) {
                        // parity compensation by DELETING an existing
                        // stair (a removal flips both leaf signs too)
                        p2.stairs.erase(p2.stairs.begin() +
                                        rng.rr((int)p2.stairs.size()));
                        p2.stairs.push_back(st[0]);
                    } else {
                        // compensating stair on a random column (repair
                        // pass relocates it if it lands on a donated one)
                        p2.stairs.push_back(st[0]);
                        int t2 = rng.rr(eng.m);
                        while (t2 == eng.tau_s) t2 = rng.rr(eng.m);
                        p2.stairs.push_back({t2, rng.rr(eng.K),
                                             rng.rr(eng.m)});
                    }
                    merged = true;
                    mergeProps++;
                }
            }
            if (!merged) mutatePlan(eng, rng, ctx, plan, worst, p2);
            if (g_repair) repairPlan(eng, rng, p2);
            // (G3) shared Metropolis draw + parity early-reject
            double u = rng.rnd();
            Engine::Eval ev2;
            if (eng.evaluateOrReject(p2, E, T, u, ev2)) {
                long long E2 = energyOf(eng, ev2, leafWeight);
                bool acc = E2 <= E;
                if (!acc) acc = u < exp(-(double)(E2 - E) / max(T, 1e-9));
                if (acc) {
                    if (merged) mergeAccs++;
                    plan = move(p2);
                    E = E2;
                    ev = ev2;
                    if (E < bestE) {
                        bestE = E; bestPlan = plan; bestEv = ev; stall = 0;
                        if (E < globalBestE) {
                            globalBestE = E;
                            atomicWrite(bestPath,
                                        planToJson(eng, plan, E, &ev.ncyc));
                        }
                        printf("  [rs %d it %lld] E=%lld ncyc=%s skipped=%d\n",
                               rs, it, E, fmtVec(ev.ncyc, eng.NCOL).c_str(),
                               ev.skipped);
                        fflush(stdout);
                    }
                }
            }
            stall++;
            if (E == 0) {
                Engine::Eval evv = eng.evaluate(plan, false);  // cache-free
                long long Ev = energyOf(eng, evv, leafWeight);
                if (Ev == 0) {
                    string js = planToJson(eng, plan, 0, &evv.ncyc);
                    atomicWrite(hitPath, js);
                    atomicWrite(hitPath + "." + tag, js);
                    printf("*** HIT: all nine returns single; witness -> %s\n",
                           hitPath.c_str());
                    fflush(stdout);
                    return 0;
                }
                // cache artifact: rebuild truth and continue
                E = Ev; ev = evv;
            }
            if (stall > stallLimit) {
                // basin hop: jump back to best, then kick
                plan = bestPlan; ev = bestEv; E = bestE;
                int kicks = 3 + rng.rr(6);
                for (int k = 0; k < kicks; k++) {
                    int w2 = 0;
                    for (int c = 1; c < eng.NCOL; c++)
                        if (ev.ncyc[c] > ev.ncyc[w2]) w2 = c;
                    mutatePlan(eng, rng, ctx, plan, w2, p2);
                    plan = p2;
                }
                if (g_repair) repairPlan(eng, rng, plan);
                ev = eng.evaluate(plan);
                E = energyOf(eng, ev, leafWeight);
                stall = 0;
            }
            if ((it + 1) % 100000 == 0) {
                double el = chrono::duration<double>(
                                chrono::steady_clock::now() - t0wall).count();
                printf("  [rs %d it %lld] cur E=%lld best E=%lld "
                       "(%.0f evals/s, %lld colors computed, "
                       "earlyrej=%lld merges=%lld/%lld signmis=%lld)\n",
                       rs, it + 1, E, bestE, eng.evalsDone / max(el, 1e-9),
                       eng.colorsComputed, eng.earlyRejects, mergeAccs,
                       mergeProps, eng.signMismatch);
                fflush(stdout);
            }
        }
        printf("[restart %d done] best E=%lld ncyc=%s\n", rs, bestE,
               fmtVec(bestEv.ncyc, eng.NCOL).c_str());
        fflush(stdout);
    }
    double el = chrono::duration<double>(chrono::steady_clock::now() -
                                         t0wall).count();
    printf("=== done: best E=%lld, %lld evals in %.1fs (%.0f evals/s) ===\n",
           globalBestE, eng.evalsDone, el, eng.evalsDone / max(el, 1e-9));
    return 2;
}

int main(int argc, char** argv) {
    vector<string> args(argv + 1, argv + argc);
    auto opt = [&](const string& name, const string& dflt) {
        for (size_t i = 0; i + 1 < args.size(); i++)
            if (args[i] == name) return args[i + 1];
        return dflt;
    };
    auto has = [&](const string& name) {
        return find(args.begin(), args.end(), name) != args.end();
    };
    int m = atoi(opt("--m", "4").c_str());
    string base = opt("--base", "growth_conjugate_base_m" + to_string(m) +
                                ".bin");
    Engine eng;
    eng.loadBase(base);
    if (eng.m != m) {
        fprintf(stderr, "base file has m=%d (asked %d)\n", eng.m, m);
        return 1;
    }
    if (has("--check-plan")) {
        vector<string> files;
        bool grab = false;
        for (auto& a : args) {
            if (a == "--check-plan") { grab = true; continue; }
            if (a.rfind("--", 0) == 0) { grab = false; continue; }
            if (grab) files.push_back(a);
        }
        return checkPlans(eng, base, files);
    }
    if (has("--anneal")) {
        u64 seed = strtoull(opt("--seed", "1").c_str(), nullptr, 10);
        long long iters = atoll(opt("--iters", "1000000").c_str());
        int restarts = atoi(opt("--restarts", "1").c_str());
        int lw = atoi(opt("--leaf-weight", "1").c_str());
        int tau = atoi(opt("--tau", "-1").c_str());
        g_earlyReject = !has("--no-early-reject");
        g_repair = !has("--no-repair");
        g_purity = !has("--no-purity");
        g_mergeProb = atof(opt("--merge-prob", "0.10").c_str());
        printf("v2 features: early-reject=%d repair=%d purity=%d "
               "merge-prob=%.3f\n", (int)g_earlyReject, (int)g_repair,
               (int)g_purity, g_mergeProb);
        return annealMain(eng, seed, iters, restarts, lw, tau,
                          opt("--tag", ""), opt("--resume", ""));
    }
    fprintf(stderr,
            "usage: %s [--m 4|6] [--base FILE] --check-plan P.json ... |\n"
            "       --anneal --seed S --iters N --restarts R "
            "[--leaf-weight W] [--tau T] [--tag TAG] [--resume P.json]\n"
            "       [--merge-prob P] [--no-early-reject] [--no-repair] "
            "[--no-purity]\n",
            argv[0]);
    return 1;
}
