load("isogeny_chain_dim2.sage")

k = 2
p = 8*3^k - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

E1 = EllipticCurve(Fp, [1,0])
# "random" isogenous curve with the same product structure
#P = E1.lift_x(2)
P = 3^k*E1.random_element()
E2 = E1.isogeny(P).codomain()

kernel = create_basis(E1, E2, 1)
H, Phi = Hessian(E1, E2, kernel)

P = E1.random_element()
Q = E2.random_element()
R = Phi(P, Q)