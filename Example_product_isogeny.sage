load("isogeny_chain_dim2.sage")

p = 4*17*3^9 - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

#construct an isogeny diamond: 17 + 8^2  = 3^4
# E1 -> E2 (17-isogeny)
E1 = EllipticCurve(Fp, [1,0])
Q = E1.lift_x(3349)
assert Q.order() == 17
phi = E1.isogeny(Q)
E2 = phi.codomain()

# kernel of (3^4,3^4)-product isogeny E1 x E2 --> E1 x E2
# K = ((phi_dual(P), 8*P) with P in E2[3^4])
# construct bases so that
# K = <(P1,Q2), (Q1,P2)>

P0,Q0 = E2.torsion_basis(3^5)
P0_3, Q0_3 = 3^4*P0, 3^4*Q0
if P0_3.weil_pairing(Q0_3,3) != omega:
	Q0 = 2*Q0

phid = phi.dual()
P1 = phid(P0)
Q1 = phid(Q0)
P2 = 8*Q0
Q2 = 8*P0

# is this step necessary (?)
e1 = P1.weil_pairing(Q1,3^5)
e2 = P2.weil_pairing(Q2,3^5)
d = e1.log(e2)
Q2 = d*Q2
assert (d % 3) == 1
assert 8*(3*P0) == 3*Q2
assert P2.weil_pairing(Q2,3^5) == e1

# sanity check (is the kernel symplectic)
1 == (3*P1).weil_pairing(3*Q1, 3^4)*(3*Q2).weil_pairing(3*P2, 3^4)

a = 0
b = 1
c = 0

(R,S),(R_9,S_9) = translate_to_Hessian((P1,P2,Q1,Q2), 5, (a,b,c))

# we need to push through an auxiliary point in order to recover the
# coefficients of the (reducible!) codomain (note we actually know them from our construction)
A = R._parent
H1,H2 = A._ellitpic_curves

aux1 = H1.map_point(E1.random_element())
aux2 = H2.map_point(E2.random_element())
auxP = A([aux1,aux2])

Phi = compute_isogeny_chain((R,S), (R_9,S_9), 4, (a,b,c), auxP=auxP); Phi

# We can recover the product structure of the codomain as follows
B = Phi.codomain()
assert B.is_reducible()
trafo = B.product_structure_transformation()
B_prod = trafo.codomain()

#we check that the elliptic curves on the codomain are correct.
H1p,H2p = B_prod.elliptic_curves()
assert H1p.j_invariant()*H2p.j_invariant() == E1.j_invariant()*E2.j_invariant()
assert H1p.j_invariant()+ H2p.j_invariant() == E1.j_invariant() + E2.j_invariant()
