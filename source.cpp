#include<bits/stdc++.h>
using namespace std;
#define rep(i,a,n) for (int i=a;i<n;i++)
//#define per(i,a,n) for (int i=n-1;i>=a;i--)
#define pb push_back
//#define mp make_pair
//#define all(x) (x).begin(),(x).end()
//#define fi first
//#define se second
typedef long long ll;
#define SZ(x) ((ll)(x).size())
typedef vector<ll> VI;
typedef pair<ll, ll> PII;
const ll m7 = 1e9 + 7, m6 = 1e9 + 6;

ll mod = 0;
ll powmod(ll a, ll b) { ll res = 1; a %= mod; assert(b >= 0); for (; b; b >>= 1) { if (b & 1)res = res * a % mod; a = a * a % mod; }return res; }
// head
int pow_mod(int a, int n, int m)
{
    if (n == 0) return 1;
    int x = pow_mod(a, n / 2, m);
    long long ans = (long long)x * x % m;
    if (n % 2 == 1) ans = ans * a % m;
    return (int)ans;
}

ll _, n;
namespace linear_seq {
    const ll N = 10010;
    ll res[N], base[N], _c[N], _md[N];
    vector<ll> Md;
    void mul(ll* a, ll* b, ll k) {
        rep(i, 0, k + k) _c[i] = 0;
        rep(i, 0, k) if (a[i]) rep(j, 0, k) _c[i + j] = (_c[i + j] + a[i] * b[j]) % mod;
        for (ll i = k + k - 1; i >= k; i--) if (_c[i])
            rep(j, 0, SZ(Md)) _c[i - k + Md[j]] = (_c[i - k + Md[j]] - _c[i] * _md[Md[j]]) % mod;
        rep(i, 0, k) a[i] = _c[i];
    }
    ll solve(ll n, VI a, VI b) { // a 系数 b 初值 b[n+1]=a[0]*b[n]+...
//        printf("%d\n",SZ(b));
        ll ans = 0, pnt = 0;
        ll k = SZ(a);
        assert(SZ(a) == SZ(b));
        rep(i, 0, k) _md[k - 1 - i] = -a[i]; _md[k] = 1;
        Md.clear();
        rep(i, 0, k) if (_md[i] != 0) Md.push_back(i);
        rep(i, 0, k) res[i] = base[i] = 0;
        res[0] = 1;
        while ((1ll << pnt) <= n) pnt++;
        for (ll p = pnt; p >= 0; p--) {
            mul(res, res, k);
            if ((n >> p) & 1) {
                for (ll i = k - 1; i >= 0; i--) res[i + 1] = res[i]; res[0] = 0;
                rep(j, 0, SZ(Md)) res[Md[j]] = (res[Md[j]] - res[k] * _md[Md[j]]) % mod;
            }
        }
        rep(i, 0, k) ans = (ans + res[i] * b[i]) % mod;
        if (ans < 0) ans += mod;
        return ans;
    }
    VI BM(VI s) {
        VI C(1, 1), B(1, 1);
        ll L = 0, m = 1, b = 1;
        rep(n, 0, SZ(s)) {
            ll d = 0;
            rep(i, 0, L + 1) d = (d + (ll)C[i] * s[n - i]) % mod;
            if (d == 0) ++m;
            else if (2 * L <= n) {
                VI T = C;
                ll c = mod - d * powmod(b, mod - 2) % mod;
                while (SZ(C) < SZ(B) + m) C.pb(0);
                rep(i, 0, SZ(B)) C[i + m] = (C[i + m] + c * B[i]) % mod;
                L = n + 1 - L; B = T; b = d; m = 1;
            }
            else {
                ll c = mod - d * powmod(b, mod - 2) % mod;
                while (SZ(C) < SZ(B) + m) C.pb(0);
                rep(i, 0, SZ(B)) C[i + m] = (C[i + m] + c * B[i]) % mod;
                ++m;
            }
        }
        return C;
    }
    ll gao(VI a, ll n) {
        VI c = BM(a);
        c.erase(c.begin());
        rep(i, 0, SZ(c)) c[i] = (mod - c[i]) % mod;
        return solve(n, c, VI(a.begin(), a.begin() + SZ(c)));
    }
};
namespace CRT {
    ll mul(ll a, ll b, ll p) {
        ll ans = 0;
        while (b) {
            if (b & 1) {
                ans = (ans + a) % p;
            }
            a = a * 2ll % p;
            b >>= 1;
        }
        return ans;
    }
    ll qp(ll a, ll b, ll mod) {
        ll ans = 1;
        while (b) {
            if (b & 1)
                ans = ans * a % mod;
            a = a * a % mod;
            b >>= 1;
        }
        return ans;
    }
    ll getInv(ll x, ll p) {
        return qp(x, p - 2, p);
    }
    ll crt(ll k, ll* n, ll* a) {
        ll sum = 1, ans = 0;
        for (int i = 1; i <= k; i++) {
            sum *= n[i];
        }
        for (int i = 1; i <= k; i++) {
            ll mi = sum / n[i];
            ans = ans + mul(mul(a[i], mi, sum), getInv(mi % n[i], n[i]), sum);
            ans %= sum;
        }
        return ans;
    }
}
ll fac[35], ans[35];
ll BM_CRT(ll n, VI& v, ll _mod) {
    // get n-th number of seq v under _mod
    ll p = 0, tmp = 2;
    while (tmp * tmp <= _mod) {
        if (_mod % tmp == 0) {
            ll sv = 1;
            while (_mod % tmp == 0) {
                _mod /= tmp;
                sv *= tmp;
            }
            fac[++p] = tmp;
        }
        tmp++;
    }
    if (_mod != 1) {
        fac[++p] = _mod;
    }
    for (int i = 1; i <= p; i++) {
        VI vv;
        for (auto t : v) {
            vv.pb(t % fac[i]);
        }
        mod = fac[i];	// important !!!
        ans[i] = linear_seq::gao(vv, n - 1);
    }
    return CRT::crt(p, fac, ans);
}