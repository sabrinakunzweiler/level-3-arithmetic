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
print(H)

J, ker = H.jacobian()
print(f"associated Jacobian is {J}")
print(f"associated (3,3)-kernel is {ker}")