#pragma GCC optimize("O3")
#pragma GCC target("avx2")
#pragma GCC optimize("Ofast")
// #pragma comment(linker, "/STACK:1073741824")

#include <bits/stdc++.h>
// #include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <functional>

using namespace __gnu_pbds;
using namespace std;
using ll = long long int;
// #define int long long int
// using ll = int;
using ull = unsigned long long;
using ld = long double;
#define pq_min priority_queue<ll, vector<ll>, greater<ll>>
// template <typename T>
// using indexed_set = __gnu_pbds::tree<T, null_type, less<T>, rb_tree_tag, tree_order_nodes_statistics_update>;

// order_of_key => number of elements less than, find_by_order => position, s.erase(s.upper_bound(x)) => erase elements
#define MOD 1000000007
#define mod 998244353
#define all(x) begin(x), end(x)
#define allr(x) rbegin(x), rend(x)
#define F first
#define S second
#define fastio                        \
    ios_base::sync_with_stdio(false); \
    cin.tie(NULL)

const unsigned gen_seed = std::chrono::system_clock::now().time_since_epoch().count();
std::mt19937_64 gen(gen_seed);

void init_code()
{
    fastio;
#ifndef ONLINE_JUDGE
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
#endif
}

struct custom_hash
{
    static uint64_t splitmix64(uint64_t x)
    {
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }

    size_t operator()(uint64_t x) const
    {
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

template <class K, class V>
using um = unordered_map<K, V, custom_hash>;

ll powermod(ll a, ll b, ll m = MOD)
{
    ll ans = 1;
    while (b > 0)
    {
        if (b & 1ll)
            ans = (1ll * (ans % m) * 1ll * (a % m)) % m;
        a = (1ll * (a % m) * 1ll * (a % m)) % m;
        b >>= 1;
    }
    return ans;
}

ll power(ll b, ll p)
{
    if (p == 0)
        return 1;
    else if (p == 1)
        return b;
    else
    {
        ll r = power(b, p / 2);
        if (p % 2 == 0)
            return (r * r);
        else
            return (((r * r)) * b);
    }
}

class DSU
{
private:
    vector<int> parent, size;

public:
    DSU(int n)
    {
        parent = vector<int>(n);
        size = vector<int>(n, 1);
        iota(begin(parent), end(parent), 0);
    }

    int getParent(int x)
    {
        if (parent[x] == x)
            return x;
        return parent[x] = getParent(parent[x]);
    }

    bool join(int x, int y)
    {
        x = getParent(x);
        y = getParent(y);

        if (x == y)
            return false;

        if (size[x] > size[y])
            swap(x, y);

        parent[x] = y;
        size[y] += size[x];
        return true;
    }

    int getSize(int x)
    {
        return size[x] = size[getParent(x)];
    }
};

struct FenwickTreeOneBasedIndexing
{
    vector<ll> bit; // binary indexed tree
    int n;

    FenwickTreeOneBasedIndexing(int n)
    {
        this->n = n + 1;
        bit.assign(n + 1, 0);
    }

    FenwickTreeOneBasedIndexing(vector<ll> a)
        : FenwickTreeOneBasedIndexing(a.size())
    {
        for (size_t i = 0; i < a.size(); i++)
            add(i, a[i]);
    }

    ll sum(int idx)
    {
        ll ret = 0;
        for (++idx; idx > 0; idx -= idx & -idx)
            ret += bit[idx];
        return ret;
    }

    ll sum(int l, int r)
    {
        return sum(r) - sum(l - 1);
    }

    void add(int idx, ll val)
    {
        for (++idx; idx < n; idx += idx & -idx)
            bit[idx] += val;
    }

    void range_add(int l, int r, ll val)
    {
        add(l, val);
        add(r + 1, -val);
    }

    int point_query(int idx)
    {
        int ret = 0;
        for (++idx; idx > 0; idx -= idx & -idx)
            ret += bit[idx];
        return ret;
    }
};

template <class S, S (*op)(S, S), S (*e)()>
struct segtree
{
public:
    int ceil_pow2(int n)
    {
        int x = 0;
        while ((1U << x) < (unsigned int)(n))
            x++;
        return x;
    }
    segtree() : segtree(0) {}
    explicit segtree(int n) : segtree(std::vector<S>(n, e())) {}
    explicit segtree(const std::vector<S> &v) : _n(int(v.size()))
    {
        log = ceil_pow2(_n);
        size = 1 << log;
        d = std::vector<S>(2 * size, e());
        for (int i = 0; i < _n; i++)
            d[size + i] = v[i];
        for (int i = size - 1; i >= 1; i--)
        {
            update(i);
        }
    }

    void set(int p, S x)
    {
        assert(0 <= p && p < _n);
        p += size;
        d[p] = x;
        for (int i = 1; i <= log; i++)
            update(p >> i);
    }

    S get(int p) const
    {
        assert(0 <= p && p < _n);
        return d[p + size];
    }

    S prod(int l, int r) const
    {
        assert(0 <= l && l <= r && r <= _n);
        S sml = e(), smr = e();
        l += size;
        r += size;

        while (l < r)
        {
            if (l & 1)
                sml = op(sml, d[l++]);
            if (r & 1)
                smr = op(d[--r], smr);
            l >>= 1;
            r >>= 1;
        }
        return op(sml, smr);
    }

    S all_prod() const { return d[1]; }

    template <bool (*f)(S)>
    int max_right(int l) const
    {
        return max_right(l, [](S x)
                         { return f(x); });
    }
    template <class F>
    int max_right(int l, F f) const
    {
        assert(0 <= l && l <= _n);
        assert(f(e()));
        if (l == _n)
            return _n;
        l += size;
        S sm = e();
        do
        {
            while (l % 2 == 0)
                l >>= 1;
            if (!f(op(sm, d[l])))
            {
                while (l < size)
                {
                    l = (2 * l);
                    if (f(op(sm, d[l])))
                    {
                        sm = op(sm, d[l]);
                        l++;
                    }
                }
                return l - size;
            }
            sm = op(sm, d[l]);
            l++;
        } while ((l & -l) != l);
        return _n;
    }

    template <bool (*f)(S)>
    int min_left(int r) const
    {
        return min_left(r, [](S x)
                        { return f(x); });
    }
    template <class F>
    int min_left(int r, F f) const
    {
        assert(0 <= r && r <= _n);
        assert(f(e()));
        if (r == 0)
            return 0;
        r += size;
        S sm = e();
        do
        {
            r--;
            while (r > 1 && (r % 2))
                r >>= 1;
            if (!f(op(d[r], sm)))
            {
                while (r < size)
                {
                    r = (2 * r + 1);
                    if (f(op(d[r], sm)))
                    {
                        sm = op(d[r], sm);
                        r--;
                    }
                }
                return r + 1 - size;
            }
            sm = op(d[r], sm);
        } while ((r & -r) != r);
        return 0;
    }

private:
    int _n, size, log;
    std::vector<S> d;

    void update(int k) { d[k] = op(d[2 * k], d[2 * k + 1]); }
};

vector<ll> primes;
bool prime[10000001 + 1];
void SieveOfEratosthenes(int n)
{
    memset(prime, true, sizeof(prime));

    for (int p = 2; p * p <= n; p++)
        if (prime[p] == true)
            for (int i = p * p; i <= n; i += p)
                prime[i] = false;

    prime[0] = false;

    for (int p = 2; p <= n; p++)
        if (prime[p])
            primes.push_back(p);
}

void SPFSieve(int n)
{
    primes.assign(n + 1, 0);
    iota(all(primes), 0);

    for (int i = 2; i * i <= n; i++)
    {
        if (primes[i] == i)
        {
            for (int j = i * i; j <= n; j += i)
                if (primes[j] == j)
                    primes[j] = i;
        }
    }
}

ll __lcm(ll a, ll b)
{
    ll gcd = __gcd(a, b);
    return (a * b) / gcd;
}

ll setBitNumber(ll n)
{
    if (n == 0)
        return 0;

    ll msb = 0;
    n = n / 2;
    while (n != 0)
    {
        n = n / 2;
        msb++;
    }

    return (1LL << msb);
}

// Returns n^(-1) mod p
unsigned long long modInverse(unsigned long long n,
                              int p)
{
    return powermod(n, p - 2, p);
}

// Returns nCr % p using Fermat's little
// theorem.
unsigned long long fac[(ll)1e6 + 5];

void factorial(ll p = MOD)
{
    fac[0] = 1;

    // precompute factorials
    for (ll i = 1; i < (ll)1e6 + 5; i++)
        fac[i] = (fac[i - 1] * i) % p;
}

unsigned long long nCrModPFermat(unsigned long long n,
                                 int r, ll p = MOD)
{
    // If n<r, then nCr should return 0
    if (n < r)
        return 0;
    // Base case
    if (r == 0)
        return 1;

    // Fill factorial array so that we
    // can find all factorial of r, n
    // and n-r
    if (fac[0] != 1)
        factorial(p);

    return (fac[n] * modInverse(fac[r], p) % p * modInverse(fac[n - r], p) % p) % p;
}

ll nCr(ll n, ll k)
{
    ld res = 1;
    for (ll i = 1; i <= k; ++i)
        res = res * (n - k + i) / i;
    return (ll)(res + 0.01);
}

ll naturalSum(ll val)
{
    ll ret = (val * 1ll * (val + 1ll)) / 2ll;
    return ret;
}

ll mul(ll a, ll b, ll m = MOD)
{
    return ((a % m) * (b % m)) % m;
}

string decimalToBinary(long n, int bits = 10)
{
    string s = "";
    for (long i = 1 << bits; i > 0; i = i / 2)
    {
        if ((n & i) != 0)
            s += '1';
        else
            s += '0';
    }

    return s;
}

bool isPrime(ll n)
{
    // Corner case
    if (n <= 1)
        return false;

    // Check from 2 to n-1
    for (ll i = 2; i * i <= n; i++)
        if (n % i == 0)
            return false;

    return true;
}

int testcase;
// Read and try to understand every single test case
// Divide test cases into cases. Almost every test case is there for a reason.
// Taking more time than expected? Open paint and start writing
// Still can't find a pattern? Write a bruteforce and look for a pattern there.
// Try to minimize code for A and B. It will almost always have a simple solution.
// __builtin_popcount(x): the number of ones in the bit representation

// find first point where prefix sum becomes negative after current index

ll op(ll a, ll b) { return min(a, b); }
ll e() { return 1e15; }

void solve()
{
    string s;
    cin >> s;

    int cur = 1, ans = 0;

    for (int i = 0; i < 4; i++)
    {
        int now = s[i] - '0';
        if (now == 0)
            now = 10;

        while (cur < now)
            cur++, ans++;
        while (cur > now)
            cur--, ans++;
    }

    cout << ans + 4 << "\n";
}

int32_t main()
{
    init_code();
    cout << fixed;

    int t = 1;
    cin >> t;

    for (testcase = 1; testcase <= t; testcase++)
    {
        // cout << "Case #" << testcase << ": ";
        solve();
    }
    return 0;
}
