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
    while True:
        R1, R2, R12 = random_points()
        T1, T2, T12 = random_points()
        RT1 = R1 + T1
        RT2 = R2 + T2
        RT1 = H1.map_point(RT1)
        RT2 = H2.map_point(RT2)
        RT12 = A([RT2,RT1])
        phi_RT12 = Phi(RT12)
    
        if prod(R12)*prod(T12)*prod(phi_RT12) != 0:
            break
    
    return (R12, T12, phi_RT12)

H = Phi.codomain()

def zero_monomial(a, b, c, d, e):
    # want for X_e to also equal say (3, 3)
    res1 = sum([ divmod(i, 3)[0] for i in [a, b, c, d, e]  ]) 
    res2 = sum([ divmod(i, 3)[1] for i in [a, b, c, d, e]  ])
    
    return (res1, res2)

def restricted_monomials(restriction):
    # restriction of the form (e, (R1, R2) )
    e, (R1, R2) = restriction
    
    return [ (i, j, n, m) 
                for i in range(9)
                for j in range(i, 9)
                for n in range(9)
                for m in range(n, 9) 
                if zero_monomial(i, j, n, m, e) == (R1, R2)
                ]

def combined_monomials(list_of_res):
    total_list = sum(list_of_res, [])
    return [ (i, j, n, m) 
                for i in range(9)
                for j in range(i, 9)
                for n in range(9)
                for m in range(n, 9) 
                if (i,j,n,m) in total_list
                ]

def point_to_monomials(triple, monomials):
    # given P = P0, ..., P8
    # given Q = Q0, ..., Q8
    # return all monomials of the form Pi*Pj*Qm*Qn
    # restriction of the form (e, (R1, R2) )
    P, Q, PQ = triple
    
    return [ P[i]*P[j]*Q[n]*Q[m] 
                ## if (i, j, n, m) in restriction_monomials else 0
                for (i, j, n, m) in monomials
             ]    
    
known_from_products = [
    (0, (3, 3)),
    (1, (3, 6)),
    (2, (3, 6)),
    (3, (6, 3)),
    (4, (6, 6)),
    (5, (6, 6)),
    (6, (6, 3)),
    (7, (6, 6)),
    (8, (6, 6)),
]

# for the first two rows, we need the first two of known_from_products
monomials_we_want = [ restricted_monomials(known_from_products[0]), restricted_monomials(known_from_products[1]) ]
res0 = restricted_monomials(known_from_products[0])
res1 = restricted_monomials(known_from_products[1])
combined = combined_monomials(monomials_we_want)

N = len(combined) - 1
print(f"{N = }")

num_samples = 2*N + 300


## still overdoing something, because now I evaluate (P, Q)
## in all _combined_ monomials
## but shoudl do this per PQ_i, right?
## for example, for PQ_0 we should only evaluate (P, Q) in the res0 monomials (instead of the combined monomials)
PQ = [get_addition_pair() for i in range(num_samples+1)]
W = [ point_to_monomials(triple, combined) for triple in PQ]
# W = [ (point_to_monomials(triple, res0), point_to_monomials(triple, res1)) for triple in PQ]
V = [ triple[2] for triple in PQ]
samples = [ (W[i], V[i]) for i in range(num_samples+1) ]

print(f"{len(samples)} samples ready")

rows = []

# row is a1*(y2 x1) + b1 ( - y1 x1)  + ... + a40 * (y2 x40) + b40 * (- y1 x40)

for x, y in samples:
    row = [ y[1] * xx for xx in x ] + [ -(y[0]) * xx for xx in x]
    # row = [ y[1] * xx for xx in x[0] ] + [ -(y[0]) * xx for xx in x[1]]
    rows.append(row)

print(f"rows = {len(rows)}")

A = Matrix(Fp, rows)

print("A ready")

K = A.right_kernel()
