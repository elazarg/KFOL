// Exhaustive candidate-table search. See probe_core_seven_models.py.
// Semilattice shapes are generated independently in Python; every carrier
// relabeling is tried for each owned choice. Owner order is suppressed.
#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
int N;
using T = string;
int at(const T &t, int x, int y) { return (unsigned char)t[x * N + y]; }
T relabel(const T &t, const vector<int> &p) {
  T out(N * N, 0);
  for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++)
      out[p[i] * N + p[j]] = p[at(t, i, j)];
  return out;
}
bool dist(const T &m, const T &a) {
  for (int x = 0; x < N; x++)
    for (int y = 0; y < N; y++)
      for (int z = y + 1; z < N; z++)
        if (at(m, x, at(a, y, z)) != at(a, at(m, x, y), at(m, x, z)))
          return false;
  return true;
}
// A distributive operation is isotone in the join order. Idempotence
// therefore puts m(x,y) above every common lower bound of x,y, and below
// x+y. Check the narrowest such intervals before full distributivity.
vector<array<int, 3>> join_bounds(const T &a) {
  vector<array<int, 3>> bounds;
  for (int x = 0; x < N; x++)
    for (int y = x + 1; y < N; y++) {
      int mask = 0, upper = at(a, x, y);
      for (int r = 0; r < N; r++) {
        if (at(a, r, upper) != upper)
          continue;
        bool valid = true;
        for (int z = 0; z < N; z++)
          if (at(a, z, x) == x && at(a, z, y) == y && at(a, z, r) != r)
            valid = false;
        if (valid)
          mask |= 1 << r;
      }
      if (mask != (1 << N) - 1)
        bounds.push_back({x, y, mask});
    }
  stable_sort(bounds.begin(), bounds.end(), [](auto x, auto y) {
    return bitset<8>(x[2]).count() < bitset<8>(y[2]).count();
  });
  return bounds;
}
bool fits_bounds(const T &t, const vector<array<int, 3>> &bounds) {
  for (auto bound : bounds)
    if (!(bound[2] & (1 << at(t, bound[0], bound[1]))))
      return false;
  return true;
}
bool pairgood(const T &a, const T &m, const T &p) {
  for (int x = 0; x < N; x++)
    for (int y = 0; y < N; y++) {
      if (at(a, at(m, x, y), at(p, x, y)) != at(a, x, y))
        return false;
      if (at(m, x, at(p, x, y)) != at(p, x, at(m, x, y)))
        return false;
    }
  for (int x = 0; x < N; x++)
    for (int y = 0; y < N; y++)
      for (int z = 0; z < N; z++) {
        int yz = at(m, y, z);
        if (at(m, x, at(p, y, yz)) != at(m, x, at(p, y, at(m, x, yz))))
          return false;
        yz = at(p, y, z);
        if (at(p, x, at(m, y, yz)) != at(p, x, at(m, y, at(p, x, yz))))
          return false;
      }
  return true;
}
bool uniondef(const T &a, array<const T *, 3> o) {
  for (int x = 0; x < N; x++)
    for (int y = x + 1; y < N; y++) {
      int v[3];
      for (int r = 0; r < 3; r++)
        v[r] = at(*o[r], x, y);
      for (int r = 0; r < 3; r++)
        if (at(*o[r], v[(r + 1) % 3], v[(r + 2) % 3]) != at(a, x, y))
          return false;
    }
  return true;
}
bool exhaustion(const T &a, array<const T *, 3> o) {
  for (int c = 0; c < N; c++) {
    int masks[3] = {0};
    for (int r = 0; r < 3; r++)
      for (int x = 0; x < N; x++)
        masks[r] |= 1 << at(*o[r], c, x);
    for (int x = 0; x < N; x++)
      if (masks[0] >> x & 1)
        for (int y = 0; y < N; y++)
          if (masks[1] >> y & 1)
            for (int z = 0; z < N; z++)
              if (masks[2] >> z & 1) {
                int v = at(a, x, at(a, y, z));
                if (at(a, c, v) != v)
                  return false;
              }
  }
  return true;
}
int root(array<int, 8> &p, int x) {
  return p[x] == x ? x : p[x] = root(p, p[x]);
}
bool irreducible(array<const T *, 3> o) {
  unsigned long long inter = (1ULL << (N * (N - 1) / 2)) - 1;
  for (int x = 0; x < N; x++)
    for (int y = x + 1; y < N; y++) {
      array<int, 8> p;
      iota(p.begin(), p.end(), 0);
      p[y] = x;
      bool changed = true;
      while (changed) {
        changed = false;
        for (int a = 0; a < N; a++)
          for (int b = a + 1; b < N; b++)
            if (root(p, a) == root(p, b))
              for (auto t : o)
                for (int z = 0; z < N; z++) {
                  int u = root(p, at(*t, a, z)), v = root(p, at(*t, b, z));
                  if (u != v) {
                    p[u] = v;
                    changed = true;
                  }
                }
      }
      int k = 0;
      for (int a = 0; a < N; a++)
        for (int b = a + 1; b < N; b++, k++)
          if (root(p, a) != root(p, b))
            inter &= ~(1ULL << k);
      if (!inter)
        return false;
    }
  return true;
}
int easy(const T &a, array<const T *, 3> o) {
  int active = 0;
  for (auto t : o)
    active += *t != a;
  if (active <= 1)
    return 1;
  bool conservative = true;
  for (int x = 0; x < N; x++)
    for (int y = x + 1; y < N; y++) {
      if (at(a, x, y) != x && at(a, x, y) != y)
        conservative = false;
      for (auto t : o)
        if (at(*t, x, y) != x && at(*t, x, y) != y)
          conservative = false;
    }
  if (conservative)
    return 2;
  for (int z = 0; z < N; z++) {
    bool ok = true;
    for (auto t : o) {
      for (int x = 0; x < N; x++)
        if (at(*t, z, x) != z)
          ok = false;
      for (int x = 0; x < N; x++)
        if (x != z)
          for (int y = 0; y < N; y++)
            if (y != z && at(*t, x, y) == z)
              ok = false;
    }
    if (ok)
      return 3;
  }
  return 0;
}
void jsonTable(ostream &f, const T &t) {
  f << '[';
  for (int x = 0; x < N; x++) {
    if (x)
      f << ',';
    f << '[';
    for (int y = 0; y < N; y++) {
      if (y)
        f << ',';
      f << at(t, x, y);
    }
    f << ']';
  }
  f << ']';
}
int main(int argc, char **argv) {
  if (argc != 4) {
    cerr << "usage: probe_core_tables SIZE SHAPES OUTPUT\n";
    return 2;
  }
  N = stoi(argv[1]);
  if (N < 1 || N > 8)
    return 2;
  ifstream in(argv[2]);
  if (!in)
    return 2;
  vector<T> shapes, tables;
  string line;
  while (in >> line) {
    if ((int)line.size() != N * N)
      return 2;
    for (char &c : line) {
      if (c < '0' || c >= '0' + N)
        return 2;
      c -= '0';
    }
    shapes.push_back(line);
  }
  unordered_set<T> seen;
  vector<int> p(N);
  iota(p.begin(), p.end(), 0);
  for (auto &t : shapes) {
    iota(p.begin(), p.end(), 0);
    do {
      auto u = relabel(t, p);
      if (seen.insert(u).second)
        tables.push_back(u);
    } while (next_permutation(p.begin(), p.end()));
  }
  cerr << "tables " << tables.size() << " shapes " << shapes.size() << endl;
  seen.clear();
  seen.rehash(0);
  ofstream out(argv[3]);
  if (!out)
    return 2;
  long long counts[4] = {}, types[4] = {};
  int shape = 0;
  auto started = chrono::steady_clock::now();
  for (auto &a : shapes) {
    vector<const T *> ops;
    auto bounds = join_bounds(a);
    for (auto &t : tables)
      if (fits_bounds(t, bounds) && dist(t, a))
        ops.push_back(&t);
    int s = ops.size();
    vector<vector<bool>> edge(s, vector<bool>(s));
    for (int i = 0; i < s; i++)
      for (int j = i; j < s; j++)
        edge[i][j] = edge[j][i] = pairgood(a, *ops[i], *ops[j]);
    for (int i = 0; i < s; i++)
      for (int j = i; j < s; j++)
        if (edge[i][j])
          for (int k = j; k < s; k++)
            if (edge[i][k] && edge[j][k]) {
              array<const T *, 3> o = {ops[i], ops[j], ops[k]};
              counts[0]++;
              if (!uniondef(a, o))
                continue;
              counts[1]++;
              if (!exhaustion(a, o))
                continue;
              counts[2]++;
              if (!irreducible(o))
                continue;
              counts[3]++;
              int type = easy(a, o);
              types[type]++;
              if (type == 0) {
                out << "[";
                jsonTable(out, a);
                out << ",[";
                for (int r = 0; r < 3; r++) {
                  if (r)
                    out << ',';
                  jsonTable(out, *o[r]);
                }
                out << "]]\n";
              }
            }
    shape++;
    if (shape % 10 == 0 || shape == (int)shapes.size()) {
      cerr << "shape " << shape << " ops " << s << " models " << counts[2]
           << " SI " << counts[3] << " hard " << types[0] << " secs "
           << chrono::duration<double>(chrono::steady_clock::now() - started)
                  .count()
           << endl;
      out.flush();
    }
  }
  cout << "{\"size\":" << N << ",\"shapes\":" << shapes.size()
       << ",\"tables\":" << tables.size() << ",\"models\":" << counts[2]
       << ",\"irreducibles\":" << counts[3] << ",\"hard\":" << types[0]
       << ",\"one_owner\":" << types[1] << ",\"conservative\":" << types[2]
       << ",\"absorbing_extensions\":" << types[3] << "}\n";
  cerr << "DONE counts";
  for (auto c : counts)
    cerr << ' ' << c;
  cerr << " types";
  for (auto c : types)
    cerr << ' ' << c;
  cerr << endl;
}
