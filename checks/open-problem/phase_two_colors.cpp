// Exhaustive mixed-adoption depths on three inputs with two posting owners.
// The underlying core has a third owner: every passive coloring on these
// two colors is proper. An extra posting color in a positive query is inert
// for the available offers, so we may keep its entries unposted.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace std;
using Mask = uint32_t;
constexpr int n = 3;
constexpr int full = 7;
constexpr int states = 8 * 8;
constexpr int infinity = 63;

struct Row {
    int head;
    array<int, 2> block;
};

struct Offer {
    int owner;
    int block;
    Mask covered;
};

static vector<Row> rows;
static vector<Mask> antichains[n];
static array<int, 512> local_index[n];
static vector<Offer> offers;

static vector<Mask> budgets;
static vector<int> order;
static vector<array<int, 14>> children;
static vector<int> free_heads;

static void build_budgets() {
    for (int head = 0; head < n; head++) {
        array<int, 2> tail{};
        int index = 0;
        for (int j = 0; j < n; j++) if (j != head) tail[index++] = j;
        for (int code = 0; code < 9; code++) {
            Row row{head, {0, 0}};
            int rest = code;
            for (int v : tail) {
                int digit = rest % 3;
                rest /= 3;
                if (digit) row.block[digit - 1] |= 1 << v;
            }
            rows.push_back(row);
        }
        for (Mask mask = 0; mask < 512; mask++) {
            bool ok = true;
            for (int i = 0; ok && i < 9; i++) if ((mask >> i) & 1) {
                auto a = rows[9 * head + i].block;
                for (int j = 0; j < 9; j++) if (i != j && ((mask >> j) & 1)) {
                    auto b = rows[9 * head + j].block;
                    if ((a[0] & b[0]) == a[0] && (a[1] & b[1]) == a[1])
                        ok = false;
                }
            }
            if (ok) {
                local_index[head][mask] = antichains[head].size();
                antichains[head].push_back(mask);
            }
        }
    }
    for (int r = 0; r < 2; r++) for (int b = 1; b <= full; b++) {
        Mask h = 0;
        for (int j = 0; j < int(rows.size()); j++)
            if ((rows[j].block[r] & b) == b) h |= Mask(1) << j;
        offers.push_back({r, b, h});
    }
    for (Mask x : antichains[0]) for (Mask y : antichains[1])
        for (Mask z : antichains[2]) budgets.push_back(x | (y << 9) | (z << 18));
    for (int id = 0; id < int(budgets.size()); id++) {
        Mask mask = budgets[id];
        int h = 0;
        for (int v = 0; v < n; v++)
            if (!(mask & (Mask(511) << (9 * v)))) h |= 1 << v;
        free_heads.push_back(h);
        array<int, 14> next;
        next.fill(-1);
        for (int j = 0; j < int(offers.size()); j++) {
            Mask residue = mask & ~offers[j].covered;
            if (residue == mask) continue;
            int code = 0;
            for (int v = 0; v < n; v++) {
                code = code * antichains[v].size() + local_index[v][(residue >> (9*v)) & 511];
            }
            next[j] = code;
        }
        children.push_back(next);
        order.push_back(id);
    }
    stable_sort(order.begin(), order.end(), [](int x, int y) {
        return popcount(budgets[x]) < popcount(budgets[y]);
    });
}

static uint8_t add_change(int value, bool changed) {
    return value == infinity ? infinity : value + int(changed);
}

static void calculate(const Row &query) {
    // Flags (last==0/1) give the bounded problem a currently active owner.
    // The blank register has last==2, encoded separately.
    using Values = array<uint8_t, states * 2>;
    vector<Values> memo(budgets.size());
    vector<uint8_t> root(budgets.size());
    array<long long, infinity + 1> hist{};
    array<int, states> eligible;
    for (int state = 0; state < states; state++) {
        int x = state / 8, y = state % 8;
        eligible[state] = x && y ? x & y : x ? x & ~query.block[0] :
            y ? y & ~query.block[1] : 1 << query.head;
    }
    int max_held = 0;
    for (int id : order) {
        auto &m = memo[id];
        for (int a = 0; a < states; a++) {
            int L = eligible[a];
            if (!L || (L & free_heads[id])) {
                m[2*a] = m[2*a+1] = L ? 0 : infinity;
                continue;
            }
            int costs[2] = {infinity, infinity};
            for (int j = 0; j < 14; j++) {
                int t = children[id][j];
                if (t < 0) continue;
                const Offer &e = offers[j];
                int b = e.owner == 0 ? e.block * 8 + a % 8 : a / 8 * 8 + e.block;
                int accepted = memo[t][2*b + e.owner];
                for (int last = 0; last < 2; last++) {
                    int v = max(memo[t][2*a+last], add_change(accepted, last != e.owner));
                    costs[last] = min(costs[last], v);
                }
            }
            for (int last = 0; last < 2; last++) {
                m[2*a+last] = costs[last];
                if (((last == 0 ? a / 8 : a % 8) != 0) && costs[last] < infinity)
                    max_held = max(max_held, costs[last]);
            }
        }
        int v = infinity;
        if (free_heads[id] & (1 << query.head)) v = 0;
        else for (int j = 0; j < 14; j++) {
            int t = children[id][j];
            if (t < 0) continue;
            const Offer &e = offers[j];
            int a = e.owner ? e.block : e.block * 8;
            v = min(v, int(max(root[t], memo[t][2*a+e.owner])));
        }
        root[id] = v;
        hist[v]++;
    }
    cout << "query " << query.head << " postings " << query.block[0] << "," << query.block[1];
    for (int d = 0; d < infinity; d++) if (hist[d]) cout << " depth" << d << "=" << hist[d];
    cout << " lose=" << hist[infinity] << " max-held=" << max_held << endl;
}

int main() {
    build_budgets();
    cout << "canonical budgets=" << budgets.size() << endl;
    // Fixing the queried head to zero loses no cases under input relabeling.
    for (int i = 0; i < 9; i++) calculate(rows[i]);
}
