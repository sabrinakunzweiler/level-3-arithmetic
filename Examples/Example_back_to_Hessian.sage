from itertools import product

load("isogeny_chain_dim2.sage")

k = 4
p = 8*3^k - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

E1 = EllipticCurve(Fp, [1,0])
# "random" isogenous curve with the same product structure
#P = E1.lift_x(2)
P = 3^5*E1.random_element()
E2 = E1.isogeny(P).codomain()

# symplectic 3^k-torsion basis
P1,P2,Q1,Q2 = create_basis(E1,E2,k,omega=omega)

# random kernel for a (3^k,3^k)-isogeny
a = ZZ.random_element(3^(k-1))
b = ZZ.random_element(3^(k-2))
c = ZZ.random_element(3^(k-1))
b = 1 + 3*b # need b!=0, so that the first isogeny is non-diagonal.

# (3^k,3^k)- group on (E1 x E2) in Hessian form (+ auxiliary information)
# where the group is <(P1 + c*Q1, b*Q2),(b*Q1, P2 + a*Q2)
(R,S),(R_9,S_9) = translate_to_Hessian((P1,P2,Q1,Q2),k,(a,b,c))

A = R._parent; A

Phi = compute_isogeny_chain((R,S), (R_9,S_9), k-1, (a,b,c)); Phi
H = Phi.codomain()

# we can push points lothrough the isogeny
H2,H1 = A._elliptic_curves
Rand1 = E1.random_element()
Rand2 = E2.random_element()
R1 = H1(Rand1)
R2 = H2(Rand2)
R12 = A([R2,R1]);
phi_R12 = Phi(R12)

# implicit test (note that addition on the Hessian is not implemented)
# R12 + first kernel generator
Test1 = Rand1 + 3*(P1 + a*Q1)
Test2 = Rand2 + 3*b*Q2
T1 = H1(Test1)
T2 = H2(Test2)
T12 = A([T2,T1])
phi_T12 = Phi(T12)


# R12 + second kernel generator
Test1 = Rand1 + 3*(b*Q1)
Test2 = Rand2 + 3*(P2 + c*Q2)
S1 = H1(Test1)
S2 = H2(Test2)
S12 = A([S2,S1])
phi_S12 = Phi(S12)


assert phi_R12 == phi_T12
assert phi_R12 == phi_S12

h0,h1,h2,h3,h4 = H._h
Ko = H.kummer_odd()
Ke = H.kummer_even()

D = H.random_point()
Do = Ko(D)
De = Ke(D)

u0, u1, u2, u3, u4 = De.coordinates()
v1, v2, v3, v4 = Do.coordinates()

M = Matrix(Fp, [
    [      -2*h1*v1,        2*h0*v1, -h4*v3 + h3*v4,  h4*v2 - h2*v4, -h3*v2 + h2*v3],
    [      -2*h2*v2, -h4*v3 - h3*v4,        2*h0*v2,  h4*v1 + h1*v4, -h3*v1 + h1*v3],
    [      -2*h3*v3, -h4*v2 - h2*v4, -h4*v1 + h1*v4,        2*h0*v3,  h2*v1 + h1*v2]
]
)

M1 = Matrix(Fp, [
    [      -2*h1*v1,        2*h0*v1, -h4*v3 + h3*v4,  h4*v2 - h2*v4, -h3*v2 + h2*v3],
    [      -2*h2*v2, -h4*v3 - h3*v4,        2*h0*v2,  h4*v1 + h1*v4, -h3*v1 + h1*v3],
    [      -2*h3*v3, -h4*v2 - h2*v4, -h4*v1 + h1*v4,        2*h0*v3,  h2*v1 + h1*v2],
    [      -2*h4*v4, -h3*v2 - h2*v3,  h3*v1 + h1*v3, -h2*v1 + h1*v2,        2*h0*v4]
])

sol0, sol1 = M.right_kernel().gens()
a = D.coordinates()[0]
b = 2*D.coordinates()[1] - v1

UU = a*sol0 + b*sol1
U0, U1, U2, U3, U4 = UU

# option = [u0, u1 + v1, u1 - v1, u2 + v2, u3 + v3, u4 + v4, u2 - v2, u4 - v4, u3 - v3]