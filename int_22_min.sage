### New interpolation code, allowing a flexible number of monomials per component

from isogeny_chain_dim2 import *

from itertools import product, combinations_with_replacement

import random
import time

# Parameters

m = 2
k = 3
l = 1
p = 2**m * 3**k * 11**l - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

# Experimentally determined minimal set of monomials for each Yi

all_non_zero_mons = [[[1, 1, 2, 2],
  [3, 3, 7, 8],
  [3, 4, 6, 8],
  [3, 4, 7, 7],
  [3, 5, 6, 7],
  [3, 5, 8, 8],
  [4, 4, 6, 7],
  [4, 4, 8, 8],
  [4, 5, 6, 6],
  [4, 5, 7, 8],
  [5, 5, 6, 8],
  [5, 5, 7, 7]],
 [[1, 8, 8, 8],
  [2, 6, 6, 8],
  [2, 6, 7, 7],
  [2, 7, 8, 8],
  [3, 3, 6, 7],
  [3, 3, 8, 8],
  [3, 4, 6, 6],
  [3, 4, 7, 8],
  [3, 5, 6, 8],
  [3, 5, 7, 7],
  [4, 4, 6, 8],
  [4, 4, 7, 7],
  [4, 5, 6, 7],
  [4, 5, 8, 8],
  [5, 5, 6, 6],
  [5, 5, 7, 8]],
 [[1, 7, 7, 8],
  [2, 6, 7, 8],
  [2, 7, 7, 7],
  [2, 8, 8, 8],
  [3, 3, 6, 8],
  [3, 3, 7, 7],
  [3, 4, 6, 7],
  [3, 4, 8, 8],
  [3, 5, 6, 6],
  [3, 5, 7, 8],
  [4, 4, 6, 6],
  [4, 4, 7, 8],
  [4, 5, 6, 8],
  [4, 5, 7, 7],
  [5, 5, 6, 7],
  [5, 5, 8, 8]],
 [[1, 5, 5, 7],
  [2, 4, 5, 7],
  [2, 5, 5, 6],
  [3, 3, 4, 5],
  [3, 5, 5, 5],
  [3, 6, 6, 6],
  [3, 6, 7, 8],
  [3, 7, 7, 7],
  [3, 8, 8, 8],
  [4, 4, 5, 5],
  [4, 6, 6, 8],
  [4, 6, 7, 7],
  [4, 7, 8, 8],
  [5, 6, 6, 7],
  [5, 6, 8, 8],
  [5, 7, 7, 8]],
 [[1, 5, 5, 8],
  [2, 4, 5, 8],
  [2, 5, 5, 7],
  [3, 3, 5, 5],
  [3, 6, 6, 7],
  [3, 6, 8, 8],
  [3, 7, 7, 8],
  [4, 4, 4, 4],
  [4, 5, 5, 5],
  [4, 6, 6, 6],
  [4, 6, 7, 8],
  [4, 7, 7, 7],
  [4, 8, 8, 8],
  [5, 6, 6, 8],
  [5, 6, 7, 7],
  [5, 7, 8, 8]],
 [[1, 5, 5, 6],
  [2, 4, 4, 7],
  [2, 5, 5, 8],
  [3, 3, 4, 4],
  [3, 6, 6, 8],
  [3, 6, 7, 7],
  [3, 7, 8, 8],
  [4, 4, 4, 5],
  [4, 6, 6, 7],
  [4, 6, 8, 8],
  [4, 7, 7, 8],
  [5, 5, 5, 5],
  [5, 6, 6, 6],
  [5, 6, 7, 8],
  [5, 7, 7, 7],
  [5, 8, 8, 8]],
 [[1, 5, 7, 8],
  [2, 5, 6, 8],
  [2, 5, 7, 7],
  [3, 3, 5, 7],
  [3, 4, 4, 7],
  [3, 4, 5, 6],
  [3, 5, 5, 8],
  [4, 4, 4, 6],
  [4, 4, 5, 8],
  [4, 5, 5, 7],
  [5, 5, 5, 6],
  [6, 6, 6, 6],
  [6, 6, 7, 8],
  [6, 7, 7, 7],
  [6, 8, 8, 8],
  [7, 7, 8, 8]],
 [[1, 5, 8, 8],
  [2, 5, 6, 6],
  [2, 5, 7, 8],
  [3, 3, 5, 8],
  [3, 4, 4, 8],
  [3, 4, 5, 7],
  [3, 5, 5, 6],
  [4, 4, 4, 7],
  [4, 4, 5, 6],
  [4, 5, 5, 8],
  [5, 5, 5, 7],
  [6, 6, 6, 7],
  [6, 6, 8, 8],
  [6, 7, 7, 8],
  [7, 7, 7, 7],
  [7, 8, 8, 8]],
 [[1, 5, 7, 7],
  [2, 5, 6, 7],
  [2, 5, 8, 8],
  [3, 3, 5, 6],
  [3, 4, 4, 6],
  [3, 4, 5, 8],
  [3, 5, 5, 7],
  [4, 4, 4, 8],
  [4, 4, 5, 7],
  [4, 5, 5, 6],
  [5, 5, 5, 8],
  [6, 6, 6, 8],
  [6, 6, 7, 7],
  [6, 7, 8, 8],
  [7, 7, 7, 8],
  [8, 8, 8, 8]]]

number_of_mons_per_component = [len(x) for x in all_non_zero_mons]

def zero_list(length):
    return [0 for _ in range(length)]

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



# !!! For some reason, the interpolation code now only finds non-trivial relations
# if we use the monomials corresponding to -Y instead of the ones for Y
# (In the end, an isogeny formula taking only a kernel as input
# won't be able to sense post-composition by an automorphism)

def get_meta_sample():
        
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

        B = Phi.codomain()

        ker_1 = Phi(A([H2(E2.zero()), H1(TT1)])) # first kernel generator of (2,2)-isogeny on B
        ker_2 = Phi(A([H2(TT2), H1(E1.zero())])) # second kernel generator
    
        if Phi != None and Psi != None:
            break
    
    end = time.time()
    
#    print(f'random (3,3)-isogeny walk took time {end-start}')
    
    # We now interpolate the (2,2)-isogeny Phi.codomain() -> Psi.codomain()
    
    def get_sample():
        
        # "Random" point on E1 x E2 of order 5^*
        Rand1 = 2**m * 3**k * E1.random_element()
        Rand2 = 2**m * 3**k * E2.random_element()
    
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
    
    def zero_list(length):
        return [0 for _ in range(length)]
    
    def get_rows(sample):
        
        P = sample[0]
        im_P = sample[1]
    
        all_monomials = [[prod(P[i] for i in mon) for mon in all_non_zero_mons[idx]] for idx in range(9)]

        minus = [0, 2, 1, 6, 8, 7, 3, 5, 4]

        rows = []

        for i in range(1, 9):
            
            betweenzeros = sum(number_of_mons_per_component[j] for j in range(1, i))
            postzeros = sum(number_of_mons_per_component[j] for j in range(i+1, 9))
    
            row = ([im_P[minus[i]] * m for m in all_monomials[0]]
                   + zero_list(betweenzeros)
                    + [-im_P[0] * m for m in all_monomials[i]]
                   + zero_list(postzeros)
                  )

            rows.append(row)
        
        return rows
    
    mat = []
    
    for s in range(max(number_of_mons_per_component) + 3):
        sample = get_sample()
        rows = get_rows(sample)
        mat += rows
    
    M = Matrix(Fp, mat)
    
    K = M.right_kernel()

#    print(f'The total dimension of the kernel is {dimension(K)}')

    assert dimension(K) == 1
    
    def is_zero(vec):
        l = len(vec)
        if list(vec) == [Fp(0) for _ in range(l)]:
            return True
        else:
            return False

    bas = K.basis()

    def count_nonzero_components(basis_vector):
    
        assert len(basis_vector) == sum(number_of_mons_per_component)
    
        non_zero_count = 0
    
        for i in range(9):
            
            lower_bound = sum(number_of_mons_per_component[:i])
            
            upper_bound = lower_bound + number_of_mons_per_component[i]
            
            component = basis_vector[lower_bound:upper_bound]
            
            if not is_zero(component):
                non_zero_count += 1

        return non_zero_count

    dim_non_triv = 0
    
    non_trivial_relations = []
    
    for b in bas:
        if count_nonzero_components(b) > 1:
            non_trivial_relations.append(b)

#    print(f'The dimension of the space of non-trivial relations is {len(non_trivial_relations)}')

    assert len(non_trivial_relations) == 1
    
    return bas[0][:12], B.zero(), ker_1, ker_2


# Guess for the required degrees

degree_in_t = 2
degree_in_r = 1
degree_in_s = 1

mons_t = [list(_) for _ in combinations_with_replacement(range(5), degree_in_t)]
mons_r = [list(_) for _ in combinations_with_replacement(range(4), degree_in_r)]
mons_s = [list(_) for _ in combinations_with_replacement(range(4), degree_in_s)]

number_of_monomials = len(mons_t) * len(mons_r) * len(mons_s)

print('Guessed degrees in t, r, s:')
print(degree_in_t, degree_in_r, degree_in_s) 

def get_rows(b0, t0, ker_1, ker_2):

    b = b0

    # The Theta null point is even by default.
    # The points generating the kernel of the (2,2)-isogeny are both odd.

    t = [t0[0], t0[1], t0[3], t0[4], t0[5]]
    
    r = [ker_1[1], ker_1[3], ker_1[4], ker_1[5]]
    
    s = [ker_2[1], ker_2[3], ker_2[4], ker_2[5]]

    all_monomials = [
        
        prod(t[j] for j in mon_t) * prod(r[j] for j in mon_r) * prod(s[j] for j in mon_s)

            for mon_t in mons_t
                for mon_s in mons_s
                    for mon_r in mons_r
        
        ]

    rows = []

    for i in range(1, 12):
        
        betweenzeros = number_of_monomials * (i - 1)
        postzeros = number_of_monomials * (12 - i - 1)

        row = ([b[i] * m for m in all_monomials]
               + zero_list(betweenzeros)
                + [-b[0] * m for m in all_monomials]
               + zero_list(postzeros)
              )

        rows.append(row)
    
    return rows

def get_rows_minimal(b0, t0, ker_1, ker_2):

    b = b0

    # The Theta null point is even by default.
    # The points generating the kernel of the (2,2)-isogeny are both odd.

    t = [t0[0], t0[1], t0[3], t0[4], t0[5]]
    
    r = [ker_1[1], ker_1[3], ker_1[4], ker_1[5]]
    
    s = [ker_2[1], ker_2[3], ker_2[4], ker_2[5]]

    all_monomials = [
        
        prod(t[j] for j in mon_t) * prod(r[j] for j in mon_r) * prod(s[j] for j in mon_s)

            for mon_t in mons_t
                for mon_s in mons_s
                    for mon_r in mons_r
        
        ]

    rows = []

    row = [b[1] * m for m in all_monomials] + [-b[0] * m for m in all_monomials]

    # Here rows is just a singleton

    rows.append(row)
    
    return rows
    

mat = []

failure = 0

for s in range(2*number_of_monomials + 50):
    try:
        rows = get_rows_minimal(*get_meta_sample())
    except:
        failure += 1
        s -= 1
        continue
    mat += rows

print(f'total number of failures: {failure}')

M = Matrix(Fp, mat)

print(f'The dimensions of M are: {M.dimensions()}')

K = M.right_kernel()

print(f'The dimension of the kernel is {K.dimension()}')

bas = K.basis()

try:
    b0 = bas[0]
    print(f'The first basis element is {b0}')
except:
    print('The kernel is trivial')

number_of_mons_per_component = [number_of_monomials for _ in range(2)]

def count_nonzero_components(basis_vector, number_of_mons_per_component):

    assert len(basis_vector) == sum(number_of_mons_per_component)

    number_of_components = len(number_of_mons_per_component)

    for i in range(number_of_components):
        
        lower_bound = sum(number_of_mons_per_component[:i])
        
        upper_bound = lower_bound + number_of_mons_per_component[i]
        
        component = basis_vector[lower_bound:upper_bound]
        
        if not is_zero(component):
            non_zero_count += 1

    return non_zero_count

dim_non_triv = 0

non_trivial_relations = []

for b in bas:
    if count_nonzero_components(b, number_of_mons_per_component) > 1:
        non_trivial_relations.append(b)

print(f'The dimension of the space of non-trivial relations is {len(non_trivial_relations)}')

try:
    b0 = non_trivial_relations[0]
    print(f'The first non-trivial relation is {b0}')
except:
    print('There are no non-trivial relations')
