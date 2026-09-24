"""Symbolic checks of the formulas in exact-blest-regions.tex.

Run from the repository root (requires SymPy 1.14.0):
    python Papers/Rockel2026ExactBlest/verify_symbolic.py
The inequalities and equality sets are proved in the manuscript. This script
independently integrates the potential derivatives, then checks the polynomial
identities used in those proofs, including the transition at w=1/2, and the
coefficient formulas of the extremal families D_c, A_w and B_b, all in the
parametrization of the paper (each parameter increases with dependence).
"""
import sympy as s

x, z, t, w, b, c = s.symbols("x z t w b c")
half = s.Rational(1, 2)
count = 0


def equal(lhs, rhs=0):
    global count
    assert s.cancel(lhs-rhs) == 0, s.factor(lhs-rhs)
    count += 1


def integral(expr, lo, hi):
    return s.integrate(expr, (t, lo, hi))


def cost(k):
    return x*x*z-k*x*z*z


def graph_regime():
    """Proposition dual-A, w in [1/2, 1)."""
    k = (3-2*w)/(2*w)
    phi0 = integral((1-t)*(2*t-k*(1-t)), 1-w, x)
    phi1 = integral((t+w-1)*(2*t-k*(t+w-1)), 1-w, x)
    psi0 = integral((t+1-w)*(t+1-w-2*k*t), 0, z)
    psi1 = psi0.subs(z, w)+integral((1-t)*(1-t-2*k*t), w, z)
    D00, D01 = phi0+psi0-cost(k), phi0+psi1-cost(k)
    D10, D11 = phi1+psi0-cost(k), phi1+psi1-cost(k)
    equal(D10, (x+w-1-z)**2*(1-w+x*(2*w-1)-2*(1-w)*z)/(2*w))
    equal((1-w+x*(2*w-1)-2*(1-w)*z)-2*(1-w)*(w-z), (2*w-1)*(x-(1-w)))
    equal(D01, (x+z-1)**2*((6-2*w)*z-(3+2*w)*x+3-4*w)/(6*w))
    equal(((6-2*w)*z-(3+2*w)*x+3-4*w).subs({x: 1-w, z: w}), 3*w)
    equal(s.diff(D00, x), (x+z-1)*((3-2*w)*z-(3+2*w)*x+3-2*w)/(2*w))
    equal(((3-2*w)*z-(3+2*w)*x+3-2*w).subs(x, 1-w), w*(2*w-1)+(3-2*w)*z)
    equal(s.diff(D00.subs(x, 1-w), z), -(1-w)*z*(3*z-2*w)/w)
    equal(s.diff(D11, z), (x+z-1)*((3-w)*z-w*x-w)/w)
    equal(((3-w)*z-w*x-w).subs(z, w), w*(2-w-x))
    equal(s.diff(D11.subs(z, w), x), (1-x)*(2*w-1)*(3-2*w-3*x)/(2*w))
    equal(D01.subs(z, 1-x))
    equal(D10.subs(z, x+w-1))
    equal(D00.subs({x: 1-w, z: 0}))
    equal(D00.subs({x: 1-w, z: w}))
    equal(D11.subs({x: 1, z: w}))
    equal(D10.subs({w: half, z: half}))
    equal(D11.subs({w: half, z: half}))


def randomized_regime():
    """Proposition dual-B, b in (0, 1/2)."""
    k, zb = 2*(1-b)/b, b/(2*(1-b))
    minus = (x-1+b)/(2*(1-b))
    plus = (1-b-x+2*b*x)/(2*(1-b))
    R0, R1 = 2*(1-b)*z+1-b, (1-b)*(1-2*z)/(1-2*b)
    phi0 = integral((1-t)*(2*t-k*(1-t)), 1-b, x)
    phi1 = integral(minus.subs(x, t)*(2*t-k*minus.subs(x, t)), 1-b, x)
    psi0 = integral(R0.subs(z, t)*(R0.subs(z, t)-2*k*t), 0, z)
    psi1 = psi0.subs(z, zb)+integral(R1.subs(z, t)*(R1.subs(z, t)-2*k*t), zb, z)
    psi2 = psi1.subs(z, b)+integral((1-t)*(1-t-2*k*t), b, z)
    D = [[s.factor(phi+psi-cost(k)) for psi in (psi0, psi1, psi2)]
         for phi in (phi0, phi1)]
    Fm = 1-b*b+(2*b-1)*x-2*(1-b)*(2-b)*z
    Fp = (1-b)*(1-3*b)+(2*b-1)*x+2*(1-b)*(2-3*b)*z
    equal(D[1][0], (x-2*(1-b)*z-(1-b))**2*Fm/(6*b*(1-b)))
    equal(D[1][1], ((1-2*b)*x+2*(1-b)*z-(1-b))**2*Fp/(6*b*(1-b)*(1-2*b)**2))
    equal(D[0][2], (x+z-1)**2*((4-3*b)*z-2*x+2-3*b)/(3*b))
    equal(((4-3*b)*z-2*x+2-3*b).subs({x: 1-b, z: b}), 3*b*(1-b))
    for j in (0, 1):
        equal(s.diff(D[0][j], x), -2*(1-x-z)*((1-b)*(1+z)-x)/b)
    equal(s.diff(D[0][0].subs(x, 1-b), z), -4*(1-b)**2*z*((2-b)*z-b)/b)
    equal(s.diff(D[0][1].subs(x, 1-b), z),
          -4*(1-b)**2*(b-z)*((2-3*b)*z-b*(1-b))/(b*(1-2*b)**2))
    equal(zb-b*(1-b)/(2-3*b), b**2*(1-2*b)/(2*(1-b)*(2-3*b)))
    equal(D[0][0].subs({x: 1-b, z: zb}), b**2*(1-2*b)/(6*(1-b)))
    equal(D[0][0].subs({x: 1-b, z: 0}))
    equal(D[0][1].subs({x: 1-b, z: b}))
    equal(s.diff(D[1][2], x),
          -(x-2*(1-b)*z-(1-b))*((1-2*b)*x+2*(1-b)*z-(1-b))/(2*b*(1-b)))
    equal((x-2*(1-b)*z-(1-b)).subs({x: 1, z: b}), -b*(1-2*b))
    equal(((1-2*b)*x+2*(1-b)*z-(1-b)).subs({x: 1-b, z: b}))
    equal(s.diff(D[1][2].subs(x, 1-b), z), (z-b)*((1-b)**2+(4-3*b)*z-1)/b)
    equal(((1-b)**2+(4-3*b)*z-1).subs(z, b), 2*b*(1-b))
    equal(D[1][0].subs(x, R0))
    equal(D[1][1].subs(x, R1))
    equal(D[0][2].subs(x, 1-z))
    equal(minus+plus, 2*x/k)
    equal(Fm.subs(z, zb), (1-2*b)*(1-x))
    equal(Fp.subs(z, zb), (1-2*b)*(1-x))
    equal(R0.subs(z, zb), 1)
    equal(R1.subs(z, zb), 1)
    equal(R1.subs(z, b), 1-b)
    equal(plus.subs(x, R1)-z)
    equal(minus.subs(x, R0)-z)


def coefficient_identities():
    eta = -1+b**3*(2*b*b-9*b+8)/(8*(1-b)**2)
    ups = b**3*(6*b*b-15*b+8)/(8*(1-b)**2)
    nb = -1+b**4*(3-2*b)/(4*(1-b)**2)
    equal(s.diff(eta, b), b**2*(2-b)*(3*b*b-8*b+6)/(4*(1-b)**3))
    equal(s.diff(ups, b), b**2*(2-3*b)*(3*b*b-8*b+6)/(4*(1-b)**3))
    equal(s.diff(ups, b)/s.diff(eta, b), (2-3*b)/(2-b))
    equal(eta+ups, -1+(2-b)*b**3/(1-b))
    equal(eta-ups, nb)
    equal(ups.subs(b, half), s.Rational(1, 8))
    equal(eta.subs(b, half), -s.Rational(3, 4))
    equal(nb.subs(b, half), -s.Rational(7, 8))
    equal((-1+(2-b)*b**3/(1-b)).subs(b, half), -s.Rational(5, 8))
    # graph regime: Upsilon, Lambda and the parameter w = ((1+e)/2)^(1/3)
    equal((2*(1-w)*w**3).subs(w, s.Rational(3, 4)), s.Rational(27, 128))
    equal(2*(2-w)*w**3-1-(2*w**3-1), 2*(1-w)*w**3)
    equal(2*(2*w**3-1)-(2*(2-w)*w**3-1), 2*w**4-1)
    equal(2*(2-w)*w**3-1, 4*w**3-2*w**4-1)


def family_moments():
    """Integrate the actual linear pieces, independently of the stated values."""
    def moment(pieces, integrand):
        return s.factor(sum(s.integrate(integrand.subs(z, branch), (x, lo, hi))
                            for lo, hi, branch in pieces))

    m = 1-c   # centre of the rank map zeta_c in the reflected coordinate x
    rho_high = [(0, m, 2*(m-x)), (m, 2*m, 2*(x-m)), (2*m, 1, x)]          # c >= 1/2
    rho_low = [(0, 2*m-1, 1-x), (2*m-1, m, 2*(m-x)), (m, 1, 2*(x-m))]      # c <= 1/2
    equal(12*moment(rho_high, x*z)-3, 1-8*(1-c)**3)
    equal(12*moment(rho_high, x*x*z)-2, 1-12*(1-c)**4)
    equal(12*moment(rho_low, x*z)-3, 8*c**3-1)
    equal(12*moment(rho_low, x*x*z)-2, 16*c**3-12*c**4-1)

    A = [(0, 1-w, 1-x), (1-w, 1, x+w-1)]
    equal(12*moment(A, x*x*z)-2, 2*(2-w)*w**3-1)
    equal(6*moment(A, x*z*(x+z))-2, 2*w**3-1)
    zb = b/(2*(1-b))
    # Here the integration variable is Z, and the branch is X=R_b(Z).
    R = [(0, zb, 2*(1-b)*x+1-b), (zb, b, (1-b)*(1-2*x)/(1-2*b)), (b, 1, 1-x)]
    equal(12*moment(R, z*z*x)-2, -1+(2-b)*b**3/(1-b))
    equal(6*moment(R, x*z*(x+z))-2, -1+b**3*(2*b*b-9*b+8)/(8*(1-b)**2))
    equal(1/(2*(1-b))+(1-2*b)/(2*(1-b)), 1)


def sharp_constant_identities():
    equal(s.Rational(1, 4)-4*c**3*(2-3*c), (2*c-1)**2*(12*c*c+4*c+1)/4)
    equal((16*c**3-12*c**4-1)-(8*c**3-1), 4*c**3*(2-3*c))
    equal(s.Rational(27, 128)-2*(1-w)*w**3,
          (4*w-3)**2*(16*w*w+8*w+3)/128)
    equal((2*w**3-1).subs(w, s.Rational(3, 4)), -s.Rational(5, 32))
    equal((2*(2-w)*w**3-1).subs(w, s.Rational(3, 4)), s.Rational(7, 128))
    etaB = -1+b**3*(2*b*b-9*b+8)/(8*(1-b)**2)
    nuB = -1+(2-b)*b**3/(1-b)
    equal(etaB.subs(b, s.Rational(1, 4)), -s.Rational(2257, 2304))
    equal(nuB.subs(b, s.Rational(1, 4)), -s.Rational(185, 192))
    equal(s.limit(etaB, b, 0), -1)
    equal(s.limit(nuB, b, 0), -1)
    # rho-family values shown in Figure 2 (c = 1/4, 1/2, 3/4)
    for cc, r, n in ((s.Rational(1, 4), -s.Rational(7, 8), -s.Rational(51, 64)),
                     (half, 0, s.Rational(1, 4))):
        equal(8*cc**3-1, r)
        equal(16*cc**3-12*cc**4-1, n)
    equal(1-8*(1-s.Rational(3, 4))**3, s.Rational(7, 8))
    equal(1-12*(1-s.Rational(3, 4))**4, s.Rational(61, 64))


if __name__ == "__main__":
    graph_regime()
    randomized_regime()
    coefficient_identities()
    family_moments()
    sharp_constant_identities()
    print(f"Verified {count} exact polynomial, derivative, contact, family-moment and constant identities.")
    print("These symbolic checks do not establish the exact-region or uniqueness theorems.")
