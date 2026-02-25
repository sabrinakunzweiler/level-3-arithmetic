"""
Finding a map from the Kummer to the abelian variety in Hesse form.
"""
R.<x> = QQ[]
K.<omega> = QQ.extension(x^2+x+1)
L.<h0,h1,h2,h3,h4,d1,d2,d3,d4,v1,v2,v3,v4> = QQ[]
#R.<> = PolynomialRing(Frac(L), order="lex")
S.<u0,u1,u2,u3,u4> = Frac(L)[]
x0 = u0
x1 = (u1 + v1) / 2
x2 = (u1 - v1) / 2
x3 = (u2 + v2) / 2
x4 = (u3 + v3) / 2
x5 = (u4 + v4) / 2
x6 = (u2 - v2) / 2
x7 = (u4 - v4) / 2
x8 = (u3 - v3) / 2


quadratics = [h0*x0^2 + h1*x1*x2 + h2*x3*x6 + h4*x5*x7 + h3*x4*x8,
h0*x1^2 + h1*x0*x2 + h3*x5*x6 + h2*x4*x7 + h4*x3*x8,
h1*x0*x1 + h0*x2^2 + h4*x4*x6 + h3*x3*x7 + h2*x5*x8,
h0*x3^2 + h1*x4*x5 + h2*x0*x6 + h3*x2*x7 + h4*x1*x8,
h0*x4^2 + h1*x3*x5 + h4*x2*x6 + h2*x1*x7 + h3*x0*x8,
h1*x3*x4 + h0*x5^2 + h3*x1*x6 + h4*x0*x7 + h2*x2*x8,
h2*x0*x3 + h4*x2*x4 + h3*x1*x5 + h0*x6^2 + h1*x7*x8,
h3*x2*x3 + h2*x1*x4 + h4*x0*x5 + h0*x7^2 + h1*x6*x8,
h4*x1*x3 + h3*x0*x4 + h2*x2*x5 + h1*x6*x7 + h0*x8^2
]

cubics = [d1*x0^3 + d1*x1^3 - 3*x0*x1*x2 + d1*x2^3 + d1*x3^3 + d1*x4^3 - 3*x3*x4*x5 + d1*x5^3 + d1*x6^3 + d1*x7^3 - 3*x6*x7*x8 + d1*x8^3,
d2*x0^3 + d2*x1^3 + d2*x2^3 + d2*x3^3 + d2*x4^3 + d2*x5^3 - 3*x0*x3*x6 + d2*x6^3 - 3*x1*x4*x7 + d2*x7^3 - 3*x2*x5*x8 + d2*x8^3,
d3*x0^3 + d3*x1^3 + d3*x2^3 + d3*x3^3 + d3*x4^3 + d3*x5^3 - 3*x1*x5*x6 + d3*x6^3 - 3*x2*x3*x7 + d3*x7^3 - 3*x0*x4*x8 + d3*x8^3,
d4*x0^3 + d4*x1^3 + d4*x2^3 + d4*x3^3 + d4*x4^3 + d4*x5^3 - 3*x2*x4*x6 + d4*x6^3 - 3*x0*x5*x7 + d4*x7^3 - 3*x1*x3*x8 + d4*x8^3,
]

#new quadratics as in Hunt:

q0 = quadratics[0]
q1 = quadratics[1] + quadratics[2]
q2 = quadratics[3] + quadratics[6]
q3 = quadratics[4] + quadratics[8]
q4 = quadratics[5] + quadratics[7]
r1 = quadratics[1] - quadratics[2]
r2 = quadratics[3] - quadratics[6]
r3 = quadratics[4] - quadratics[8]
r4 = quadratics[5] - quadratics[7]


new_quadratics = [2*q0,q1,q2,q3,q4,r1,r2,r3,r4]
qq = [2*q0, q1, q2, q3, q4]
uu = [u0,u1,u2,u3,u4]
rr = [r1,r2,r3,r4]
for el in rr:
	el.monomials() == uu

M1 = 2*Matrix([[ri.monomial_coefficient(ui) for ui in uu] for ri in rr])
#sol = M.right_kernel().gens()[0]

## now xi should be a*sol + v

M = 2*Matrix([[ri.monomial_coefficient(ui) for ui in uu] for ri in rr[:3]])
sol1,sol2 = M.right_kernel().gens()

# some (not elegant) simplifications
el1 = gcd(sol1)
el2 = gcd(sol2)
sol1 = sol1/el1
sol2 = sol2/el2
sol1 = vector([L(el) for el in sol1])
sol2 = vector([L(el) for el in sol2])
#
# again
el1 = gcd(sol1)
el2 = gcd(sol2)
sol1 = sol1/el1
sol2 = sol2/el2
sol1 = vector([L(el) for el in sol1])
sol2 = vector([L(el) for el in sol2])

sol1 = sol1/sol1[0].coefficients()[0]
sol2 = sol2/sol2[1].coefficients()[0]

T.<a,b> = Frac(L)[]
uu = a*sol1 + b*sol2

eqs = []
# find solution for a, b so that the following are all zero (modulo the Kummer equation)
for el in new_quadratics:
	eqs.append(el(uu[0], uu[1], uu[2], uu[3], uu[4]))

# Kummer equation:
Kummer_eq = h0*h2^2*v1^3*v2 + h1*h3*h4*v1^3*v2 - h0*h1^2*v1*v2^3 - h2*h3*h4*v1*v2^3 + h0*h3^2*v1^3*v3 + h1*h2*h4*v1^3*v3 - h0*h3^2*v2^3*v3 - h1*h2*h4*v2^3*v3 - h0*h1^2*v1*v3^3 - h2*h3*h4*v1*v3^3 + h0*h2^2*v2*v3^3 + h1*h3*h4*v2*v3^3 + h1*h2*h3*v1^3*v4 + h0*h4^2*v1^3*v4 + h1*h2*h3*v2^3*v4 + h0*h4^2*v2^3*v4 + 4*h0^3*v1*v2*v3*v4 + h1^3*v1*v2*v3*v4 + h2^3*v1*v2*v3*v4 + h3^3*v1*v2*v3*v4 + h4^3*v1*v2*v3*v4 - h1*h2*h3*v3^3*v4 - h0*h4^2*v3^3*v4 - h0*h1^2*v1*v4^3 - h2*h3*h4*v1*v4^3 - h0*h2^2*v2*v4^3 - h1*h3*h4*v2*v4^3 + h0*h3^2*v3*v4^3 + h1*h2*h4*v3*v4^3
I = L.ideal(Kummer_eq)

unknowns = [a^2, a*b, b^2, T(1)]
Q1_mod = Matrix(L.quotient(I), [[qi.monomial_coefficient(u) for u in unknowns] for qi in eqs])

SOL = Q1_mod.right_kernel()