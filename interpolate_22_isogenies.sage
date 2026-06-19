from isogeny_chain_dim2 import *

from itertools import product, combinations_with_replacement

import random
import time

K.<w> = NumberField(x^2+x+1)
R.<X0,X1,X2,X3,X4,X5,X6,X7,X8> = K[]

vec = [X0, X1, X2, X3, X4, X5, X6, X7, X8]

tau1 = [1, w, w^2, 1, w, w^2, 1, w, w^2]
tau2 = [1, 1, 1, w, w, w, w^2, w^2, w^2]

def sigma1(idx):
    return [1, 2, 0, 4, 5, 3, 7, 8, 6][idx]

def sigma2(idx):
    return [3, 4, 5, 6, 7, 8, 0, 1, 2][idx]

def test_tuple(tup, idx):

    # Check whether the monomial mon defined by tup satisfies (mon \circ tau_i)[idx] = (tau_i \circ mon)[idx] for i = 1,2

    if tau1[idx] == prod([tau1[a] for a in tup]) and tau2[idx] == prod([tau2[a] for a in tup]):
        return True
    else:
        return False

# Expected degree of the monomials occuring in the formula
monomial_degree = 4

# For now, only allows monomial degrees that are not 0 mod 3
assert monomial_degree%3

# Monomials expected to appear in Y0
mons0 = [
    list(t)
    for t in combinations_with_replacement(range(9), monomial_degree)
    if test_tuple(t, 0)
]

# List of all monomials per index

all_mons = [
    
    [
        list(t)
        for t in combinations_with_replacement(range(9), monomial_degree)
        if test_tuple(t, idx)
    ]

    for idx in range(9)
    
]

number_of_mons = len(all_mons[0])

assert prod(number_of_mons == len(all_mons[i]) for i in range(9))


# Isolate the computation of the (3,3)-isogeny chain as a separate function

def compute_33_chain(E1, E2, P1, P2, Q1, Q2, k, a, b, c):
    
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
        return Phi, H1, H2, A
    else:
        raise Exception("Something went wrong")

# Parameters

k = 4
l = 6
p = 8 * 3**k * 5**l - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

# !!! For some reason, the interpolation code now only finds non-trivial relations
# if we use the monomials corresponding to -Y instead of the ones for Y
# (In the end, an isogeny formula taking only a kernel as input
# won't be able to sense post-composition by an automorphism)

while True:
        
    ## Interpolate (2,2)-isogeny formula on a random abelian surface
    
    # We first sample a random abelian surface as the image of a (3,3)-isogeny chain
    # coming from E1 x E2, where E2 is isogenous to E1
    
    start = time.time()

    while True:
        
        E1 = EllipticCurve(Fp, [1,0])
        # "random" isogenous curve with the same product structure
        #P = E1.lift_x(2)
        P = E1.random_element()
        E2 = E1.isogeny(P, algorithm = 'factored').codomain()
        
        basis1 = E1.torsion_basis(2)
        basis2 = E2.torsion_basis(2)
        
        TT1s = [basis1[0], basis1[1], basis1[0]+basis1[1]]
        TT2s = [basis2[0], basis2[1], basis2[0]+basis2[1]]
    
        # We take a random point of order 2 on E1 and E2
    
        TT1 = random.choice(TT1s)
        TT2 = random.choice(TT2s)
    
        # Construct corresponding 2-isogenies
    
        eps1 = E1.isogeny(TT1)
        eps2 = E2.isogeny(TT2)
    
        EE1 = eps1.codomain()
        EE2 = eps2.codomain()
    
        # F1 and F2 are 2-isogenous to E1 and E2 respectively
    
        # The kernel of the diagonal (2,2)-isogeny (E1 x E2) -> (F1 x F2)
    
        kernel_diagonal_22iso = [[TT1, E2.zero()], [E1.zero(), TT2], [TT1, TT2], [E1.zero(), E2.zero()]]
    
        # symplectic 3^k-torsion basis
        P1,P2,Q1,Q2 = create_basis(E1,E2,k,omega=omega)
        
        # random kernel for a (3^k,3^k)-isogeny
        a = ZZ.random_element(3^(k-1))
        b = ZZ.random_element(3^(k-2))
        c = ZZ.random_element(3^(k-1))
        b = 1 + 3*b # need b!=0, so that the first isogeny is non-diagonal.
    
        Phi, H1, H2, A = compute_33_chain(E1, E2, P1, P2, Q1, Q2, k, a, b, c)
    
        Psi, HH1, HH2, AA = compute_33_chain(EE1, EE2, eps1(P1), eps2(P2), eps1(Q1), eps2(Q2), k, a, b, c)
    
        if Phi != None and Psi != None:
            break
    
    end = time.time()
    
#    print(f'random (3,3)-isogeny walk took time {end-start}')
    
    # We now interpolate the (2,2)-isogeny Phi.codomain() -> Psi.codomain()
    
    def get_sample():
        
        # "Random" point on E1 x E2 of order 5^*
        Rand1 = 8 * 3**k * E1.random_element()
        Rand2 = 8 * 3**k * E2.random_element()
    
        # Image of random point under Phi
        R1 = H1(Rand1)
        R2 = H2(Rand2)
        R12 = A([R2, R1])
        phi_R12 = Phi(R12)
        
        # Image of random point under Psi \circ (eps1 x eps2)
        RR1 = HH1(eps1(Rand1))
        RR2 = HH2(eps2(Rand2))
        RR12 = AA([RR2, RR1])
        psi_RR12 = Psi(RR12)
    
        return (phi_R12, psi_RR12)
    
    ls = len(mons0) # total number of monomials
    
    def zero_list(length):
        return [0 for _ in range(length)]
    
    def get_rows(sample):
        
        P = sample[0]
        im_P = sample[1]
    
        all_monomials = [[prod(P[i] for i in mon) for mon in all_mons[idx]] for idx in range(9)]

        minus = [0, 2, 1, 6, 8, 7, 3, 5, 4]

        rows = []

        for i in range(1, 9):
            
            betweenzeros = number_of_mons * (i - 1)
            postzeros = number_of_mons * (9 - i - 1)
    
            row = ([im_P[minus[i]] * m for m in all_monomials[0]]
                   + zero_list(betweenzeros)
                    + [-im_P[0] * m for m in all_monomials[i]]
                   + zero_list(postzeros)
                  )

            rows.append(row)
        
        return rows
    
    mat = []
    
    for s in range(number_of_mons + 2):
        sample = get_sample()
        rows = get_rows(sample)
        mat += rows
    
    M = Matrix(Fp, mat)
    
    K = M.right_kernel()

    print(f'The total dimension of the kernel is {dimension(K)}')
    
    def is_zero(vec):
        l = len(vec)
        if list(vec) == [Fp(0) for _ in range(l)]:
            return True
        else:
            return False

    bas = K.basis()

    break

def count_nonzero_components(basis_vector):
    
    assert len(basis_vector) == 9 * number_of_mons

    non_zero_count = 0

    for i in range(9):
        
        lower_bound = number_of_mons * i
        
        upper_bound = number_of_mons * (i + 1)
        
        component = basis_vector[lower_bound:upper_bound]
        
        if not is_zero(component):
            non_zero_count += 1

    return non_zero_count

dim_non_triv = 0

for b in bas:
    if count_nonzero_components(b) > 1:
        dim_non_triv += 1

print(f'The dimension of the space of non-trivial relations is {dim_non_triv}')
