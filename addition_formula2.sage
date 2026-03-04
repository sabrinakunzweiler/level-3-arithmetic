R.<t1,t2,t3,t4> = ZZ[]

# c0 = 0
# c1 = t1*t2
# c2 = t2*t3
# c3 = -t2*t4
# c4 = -t1*t2
# c5 = 0
# c6 = -t1*t3
# c7 = -t1*t4
# c8 = -t2*t3
# c9 = t1*t3
# c10 = 0
# c11 = t3*t4
# c12 = t2*t4
# c13 = t1*t4
# c14 = -t3*t4
# c15 = 0

# # addition matrix
# add_M = Matrix(R, [
#     [c5,c4,c6,c7],
#     [c1,c0,c2,c3],
#     [c9,c8,c10,c11],
#     [c13,c12,c14,c15]
# ])

add_M = Matrix(R, [
    [     0, -t1*t2, -t1*t3, -t1*t4],
    [ t1*t2,      0,  t2*t3, -t2*t4],
    [ t1*t3, -t2*t3,      0,  t3*t4],
    [ t1*t4,  t2*t4, -t3*t4,      0]
])

def vector_form(P):
    A0, A1, A2, A3, A4, A5, A6, A7, A8 = P
    VA0 = vector([A1*A2, A3*A6, A4*A8, A5*A7])
    VA1 = vector([A0*A1, A5*A8, A3*A7, A4*A6])
    VA2 = vector([A0*A2, A4*A7, A5*A6, A3*A8])
    VA3 = vector([A7*A8, A0*A3, A1*A5, A2*A4])
    VA4 = vector([A6*A7, A5*A2, A0*A4, A1*A3])
    VA5 = vector([A6*A8, A4*A1, A2*A3, A0*A5])
    VA6 = vector([A4*A5, A0*A6, A2*A7, A1*A8])
    VA7 = vector([A3*A4, A2*A8, A1*A6, A0*A7])
    VA8 = vector([A3*A5, A1*A7, A0*A8, A2*A6])

    return [VA0,VA1,VA2,VA3,VA4,VA5,VA6,VA7,VA8]

def add(P, Q, B, odd_two_torsion_point):
    # P and Q are points on the Abelian surface B
    _,t1,_,t2,t3,t4,_,_,_ = odd_two_torsion_point
    mat = add_M(t1,t2,t3,t4)
    vec1, vec2 = vector_form(P), vector_form(Q)
    result = []
    for i in range(9):
        result.append(vec2[i] * mat * vec1[i])

    return B(result)

### Let's test the formula

# Example field
k = 4
p = 8*3**k - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p**2, modulus=x**2+x+1)
omega = om

from isogeny_chain_dim2 import *
from itertools import product

def test_formula():
    
    # We first sample a random abelian surface as the image of a (3,3)-isogeny chain
    # coming from E1 x E2, where E2 is isogenous to E1
    
    while True:
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
        # where the group is <(P1 + a*Q1, b*Q2),(b*Q1, P2 + c*Q2)
        (R,S),(R_9,S_9) = translate_to_Hessian((P1,P2,Q1,Q2),k,(a,b,c),E1,E2)
        
        A = R._parent
        
        Phi = compute_isogeny_chain((R,S), (R_9,S_9), k-1, (a,b,c))
        
        # we can push points through the isogeny
        H2,H1 = A._elliptic_curves
        Rand1 = E1.random_element()
        Rand2 = E2.random_element()
        R1 = H1.map_point(Rand1)
        R2 = H2.map_point(Rand2)
        R12 = A([R2,R1]);
        phi_R12 = Phi(R12)
        
        # implicit test (note that addition on the Hessian is not implemented)
        # R12 + first kernel generator
        Test1 = Rand1 + 3*(P1 + a*Q1)
        Test2 = Rand2 + 3*b*Q2
        T1 = H1.map_point(Test1)
        T2 = H2.map_point(Test2)
        T12 = A([T2,T1])
        phi_T12 = Phi(T12)
        
        # R12 + second kernel generator
        Test1 = Rand1 + 3*(b*Q1)
        Test2 = Rand2 + 3*(P2 + c*Q2)
        S1 = H1.map_point(Test1)
        S2 = H2.map_point(Test2)
        S12 = A([S2,S1])
        phi_S12 = Phi(S12)
        
        if (phi_R12 == phi_S12 and phi_R12 == phi_T12):
            break
    
    # We construct an odd two torsion point on E1 x E2

    TT1, TT2 = E1.torsion_basis(2)[0], E2.zero()
    
    odd_two_torsion_point0 = A([H2(TT2), H1(TT1)])

    def random_points():
        Rand1 = E1.random_element() + TT1
        Rand2 = E2.random_element() + TT2
        R1 = H1(Rand1)
        R2 = H2(Rand2)
        R12 = A([R2,R1])
        phi_R12 = Phi(R12)
        return (Rand1, Rand2, phi_R12)
    
    def get_sample():
        while True:
            R1, R2, R12 = random_points()
            T1, T2, T12 = random_points()
            RT1 = R1 + T1 - TT1
            RT2 = R2 + T2 - TT2
            RT1 = H1(RT1)
            RT2 = H2(RT2)
            RT12 = A([RT2,RT1])
            phi_RT12 = Phi(RT12)
        
            if prod(R12)*prod(T12)*prod(phi_RT12) != 0:
                break
        
        return R12, T12, phi_RT12
    
    P,Q,PQ = get_sample()
    
    odd_two_torsion_point1 = Phi(odd_two_torsion_point0)
    
    B = Phi.codomain()
    
    return add(P, Q, B, odd_two_torsion_point1) == PQ

print(test_formula())
