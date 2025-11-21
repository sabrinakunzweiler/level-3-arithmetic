load("hessian_arithmetic_dim1.py")
load("three_isogenies_dim1.py")

p = 8*3^10 - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<a> = GF(p^2, modulus=x^2+x+1)
omega = a

E = EllipticCurve(Fp, [1,0])

P,Q = E.torsion_basis(3^10)
P3 = 3^9*P
Q3 = 3^9*Q

# the isomorphism to the Hessian curve is defined by the 3-torsion basis
H = EllipticCurveHessianForm(E, basis=[P3,Q3])
Hb = H.kummer()

# can compute isogenies with kernel  3*(P + a*Q) for arbitrary values a

P3_H = H.map_point(P3)
P3_K = Hb(P3_H)
phi = ThreeIsogenyKummer(P3_K)


P = P + 10*Q
P_H = H.map_point(P)
P_K = Hb(P_H)

Phi = Three_N_IsogenyKummer(P_K, 9)