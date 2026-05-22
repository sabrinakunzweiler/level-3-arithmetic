from itertools import product

load("isogeny_chain_dim2.sage")

k = 4
p = 8*3^k - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om
exp3 = (p**2 - 1) // 3

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

# coordinate Z is of the form 
# apply inv coords, apply hadamard
λ0, λ1, λ2, λ3, λ4 = [ 1/d for d in H._d]

def ZZZ(P):
    x0, x1, x2, x3, x4, x5, x6, x7, x8 = P.coordinates()
    return λ0*x0 + λ1*x1 + λ1*x2 + λ2*x3 + λ3*x4 + λ4*x5 + λ2*x6 + λ4*x7 + λ3*x8


# in general, the cubical formula is simply
# Z(M_P. Q~) Z(0~) / Z(M_P. 0~) Z(Q~)
# for any cubical point Q~, 0~ above Q, 0.

def tate_pairing_P1(Q):      
    return (ZZZ(Q._add_P1()) * ZZZ(H.zero()) ) / (ZZZ(H.zero()._add_P1()) * ZZZ(Q)) 

def tate_pairing_P2(Q):      
    return (ZZZ(Q._add_P2()) * ZZZ(H.zero()) ) / (ZZZ(H.zero()._add_P2()) * ZZZ(Q)) 

def tate_pairing_Q1(Q):      
    return (ZZZ(Q._add_Q1()) * ZZZ(H.zero()) ) / (ZZZ(H.zero()._add_Q1()) * ZZZ(Q)) 

def tate_pairing_Q2(Q):      
    return (ZZZ(Q._add_Q2()) * ZZZ(H.zero()) ) / (ZZZ(H.zero()._add_Q2()) * ZZZ(Q)) 

def reduced_P1(Q):
    return tate_pairing_P1(Q)**exp3
def reduced_P2(Q):
    return tate_pairing_P2(Q)**exp3
def reduced_Q1(Q):
    return tate_pairing_Q1(Q)**exp3
def reduced_Q2(Q):
    return tate_pairing_Q2(Q)**exp3

def tate_profile(Q):  
    return [ f(Q) for f in [reduced_P1, reduced_P2, reduced_Q1, reduced_Q2]]

# these should be the weil pairings on our symplectic basis
# and this verifies that indeed we get a symplectic basis
# which is a good sign!
print(tate_pairing_P1(Q1) / tate_pairing_Q1(P1) == om)
print(tate_pairing_P1(Q2) / tate_pairing_Q2(P1) ==  1)
print(tate_pairing_P2(Q2) / tate_pairing_Q2(P2) == om)
print(tate_pairing_P2(Q1) / tate_pairing_Q1(P2) ==  1)

# what are some other ways in which we could verify the pairing?
# triviality of the Tate pairing should check divisibility by [3] on A(Fq)
# so at least P1, P2, Q1, Q2 should have a trivial profile...
print(tate_profile(P1))
print(tate_profile(P2))
print(tate_profile(Q1))
print(tate_profile(Q2))

## lets try bilinearity
score = 0
for i in range(10):
    Q = H.random_point()
    R = H.random_point()
    if (reduced_P1(Q)*reduced_P1(R) == reduced_P1(Q+R)):
        score += 1
print(score)