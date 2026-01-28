from itertools import product

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
R1 = H1.map_point(Rand1)
R2 = H2.map_point(Rand2)
R12 = A([R2,R1]);
phi_R12 = Phi(R12)

# implicit test (note that addition on the Hessian is not implemented)
# R12 + first kernel generator
Test1 = Rand1 + 3*(P1 + c*Q1)
Test2 = Rand2 + 3*b*Q2
T1 = H1.map_point(Test1)
T2 = H2.map_point(Test2)
T12 = A([T2,T1])
phi_T12 = Phi(T12)

phi_R12 == phi_T12

# R12 + second kernel generator
Test1 = Rand1 + 3*(b*Q1)
Test2 = Rand2 + 3*(P2 + a*Q2)
S1 = H1.map_point(Test1)
S2 = H2.map_point(Test2)
S12 = A([S2,S1])
phi_S12 = Phi(S12)

phi_R12 == phi_S12


####################################
####################################
## trying addition formulas

def random_points():
    Rand1 = E1.random_element()
    Rand2 = E2.random_element()
    R1 = H1.map_point(Rand1)
    R2 = H2.map_point(Rand2)
    R12 = A([R2,R1])
    phi_R12 = Phi(R12)
    return (Rand1, Rand2, phi_R12)

def get_addition_pair():
    R1, R2, R12 = random_points()
    T1, T2, T12 = random_points()
    RT1 = R1 + T1
    RT2 = R2 + T2
    RT1 = H1.map_point(RT1)
    RT2 = H2.map_point(RT2)
    RT12 = A([RT2,RT1])
    phi_RT12 = Phi(RT12)
    return (R12, T12, phi_RT12)

H = Phi.codomain()


def to_monomials(triple):
    # given P = P0, ..., P8
    # given Q = Q0, ..., Q8
    # return all monomials of the form Pi*Pj*Qm*Qn
    P, Q, PQ = triple
    
    return [P[i]*P[j]*Q[n]*Q[m]
                for i in range(9)
                for j in range(i, 9)
                for n in range(9)
                for m in range(n, 9) 
                
                if (i + j + n + m) in {12, 13, 14, 16, 17, 18, 19} 
                
                ]
    

known_monomials = [
    [ 4, 8, 0, 0],
    [ 3, 6, 1, 2],
    [ 2, 4, 2, 4],
    [ 1, 2, 3, 6],
    [ 0, 0, 4, 8],
    
    [ 3, 7, 2, 2],
    [ 5, 8, 0, 1],
    [ 7, 0, 7, 0],
    [ 0, 1, 5, 8],
    [ 2, 2, 3, 7],
    
    [ 4, 7, 0, 2],
    [ 3, 8, 1, 1],
    ##???    
     [1, 1, 3, 8],
     [0, 2, 4, 7],
     
    [ 7, 8, 0, 3],
    [ 6, 6, 1, 5],
    ##???
    [1, 5, 6, 6],
    [0, 3, 7, 8],
     
    [ 8, 8, 0, 4],
    [ 6, 7, 2, 5],
    [ 4, 6, 4, 6],
    [ 2, 5, 6, 7],
    [ 0, 4, 8, 8],
    
    
]

N = len(to_monomials(get_addition_pair())) - 1
print(f"{N = }")
U = 9*N


PQ = [get_addition_pair() for i in range(N+1)]
W = [ to_monomials(triple) for triple in PQ]
V = [ triple[2] for triple in PQ]
samples = [ (W[i], V[i]) for i in range(N+1) ]

print("samples ready")

rows = []
for x, y in samples:
    for a in range(9):
        for b in range(a+1, 9):
            row = {}
            for c in range(N):
                row[a*N + c] = y[b] * x[c]
                row[b*N + c] = -y[a] * x[c]
            rows.append(row)

print(f"rows = {len(rows)}")

A = Matrix(Fp, len(rows), U, sparse=True)
for i, row in enumerate(rows):
    for j, v in row.items():
        A[i, j] = v

K = A.right_kernel()
