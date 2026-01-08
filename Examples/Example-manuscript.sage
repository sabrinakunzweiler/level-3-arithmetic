# Example (Section 7)
load("isogeny_chain_dim2.sage")

# Setup
Fp = FiniteField(2*5*3^3-1)
R.<x> = Fp[]
K.<om> = Fp.extension(x^2+x+1)

E0 = EllipticCurve(K,[0,1])
P27 = E0([252,71])
Q27 = E0([7*om, 13*om+141])

e27 = P27.weil_pairing(Q27,27)
assert e27.multiplicative_order() == 27

# commutative diagram
P5 = E0.lift_x(8)
assert P5.order() == 5
E1 = E0
phi = E0.isogeny(P5)
E2 = phi.codomain()

P1,Q1 = 2*P27, 2*Q27
P2,Q2 = phi(Q27), phi(P27)

# transformation to Hesse form
P1_9,Q1_9 = 3*P1, 3*Q1
P2_9,Q2_9 = 3*P2, 3*Q2
P1_3,Q1_3 = 9*P1, 9*Q1
P2_3,Q2_3 = 9*P2, 9*Q2

H1 = EllipticCurveHessianForm(E1, basis=[P1_3,Q1_3])
H2 = EllipticCurveHessianForm(E2, basis=[P2_3,Q2_3])
A0 = AbelianSurfaceHessianForm([H2,H1], omega=om)

M1 = Matrix([[1,0,231*om], [1,19*om, 19*om],[1,250*om, 19*om]])
M2 = Matrix([[1,0,179],[-9*om^2,9*(1-om),-220*om^2],[-9*om^2, 9*(om-1),-220*om^2]])

#Test1 = M1*vector(P1)
#Test2 = M2*vector(P2)

R1 = H1.map_point(P1)
R2 = H2.map_point(Q2)
S1 = H1.map_point(Q1)
S2 = H2.map_point(P2)

R = A0([R2,R1])
S = A0([S2,S1])

R1_9 = H1.map_point(P1_9)
R2_9 = H2.map_point(Q2_9)
S1_9 = H1.map_point(Q1_9)
S2_9 = H2.map_point(P2_9)

R_9 = A0([R2_9,R1_9])
S_9 = A0([S2_9,S1_9])

aux1 = H1.map_point(E1.random_element())
aux2 = H2.map_point(E2.random_element())
auxP = A0([aux2,aux1])

Phi = compute_isogeny_chain((R,S), (R_9,S_9), 2, (0,1,0), auxP=auxP);

#(R,S),(R_9,S_9) = translate_to_Hessian((P1,P2,Q1,Q2), 3, (0,1,0))

# by construction, (R,S) = (P1+Q2, P2+Q1) where P1,P2,Q1,Q2 is the canonical basis
# transformation (R,S) -> (P1,P2) is given by scalars (1,1,1,omega^2,omega)
t = A0.symplectic_transformation(0,1,0)
t._scalars == (1,1,1,om^2,om)
X_9 = t(R_9)
Y_9 = t(S_9)



