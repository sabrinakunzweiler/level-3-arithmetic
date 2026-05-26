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

H = Phi.codomain()
P = H.random_point()

# this works
Q = P + P

# this should be zero
assert (p+1)*P == H.zero()

# we can recreate the canonical basis
P1, P2, Q1, Q2 = H.canonical_basis()


# these should be the weil pairings on our symplectic basis
# and this verifies that indeed we get a symplectic basis
# which is a good sign!
assert (Q1.tate_pairing_P1() / P1.tate_pairing_Q1() == om)
assert (Q2.tate_pairing_P1() / P1.tate_pairing_Q2() ==  1)
assert (Q2.tate_pairing_P2() / P2.tate_pairing_Q2() == om)
assert (Q1.tate_pairing_P2() / P2.tate_pairing_Q1() ==  1)
print("symplicity check is OK")

# what are some other ways in which we could verify the pairing?
# triviality of the Tate pairing should check divisibility by [3] on A(Fq)
# so at least P1, P2, Q1, Q2 should have a trivial profile...
assert P1.tate_profile(3) == [1, 1, 1, 1]
assert P2.tate_profile(3) == [1, 1, 1, 1]
assert Q1.tate_profile(3) == [1, 1, 1, 1]
assert Q2.tate_profile(3) == [1, 1, 1, 1]
print("trivial profile check is OK")

## lets try bilinearity
score = 0
for i in range(10):
    Q = H.random_point()
    R = H.random_point()
    if Q.reduced_tate_P1() * R.reduced_tate_P1() == (Q+R).reduced_tate_P1():
        score += 1

if score == 10:
    print("bilinearity is checked!")

## a nice tool to check divisibility
for i in range(10):
    Q = H.random_point()
    if Q.tate_profile(3) == [1, 1, 1, 1]:
        assert (((p+1) // 3)*Q).is_zero()
    else:
        assert (3*Q).tate_profile(3) == [1, 1, 1, 1]
print("divisibility is checked!")


# efficiently sample a point above any canonical 3-torsion basis element
R = H.sample_above(P1)
print(f"R has profile {R.tate_profile(3)}")
print(f"R is above P1: {((p+1) // 3)*R == P1}")

# above P1 <--> [   1,    1, om,  1]
# above P2 <--> [   1,    1,  1, om]
# above Q1 <--> [om^2,    1,  1,  1]
# above Q2 <--> [   1, om^2,  1,  1]