from isogeny_chain_dim2 import *

from itertools import product, combinations_with_replacement

k = 4
p = 8*3^k - 1
F1 = GF(p)
R.<x> = F1[]
Fp.<om> = GF(p^2, modulus=x^2+x+1)
omega = om

def get_meta_sample():
    ## Interpolate addition formulae on a random abelian surface
    
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
            
    TT1, TT2 = E1.torsion_basis(2)[0], E2.zero()
    
    odd_point = A([H2(TT2), H1(TT1)])
    
    # We now interpolate the addition formulae on our randomly generated surface
    
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
    
    def index_to_mons(index):
        i0 = index%3
        i1 = index//3
        mons = [(c00+3*c01,c10+3*c11)
                for c00 in range(3)
                for c01 in range(3)
                for c10 in range(3)
                for c11 in range(3)
                if (c00 + c10)%3 == i0
                and (c01 + c11)%3 == i1
                and 3*c11+c10 > 3*c01+c00]
        return mons
        
    def square_mons(mons):
        mons = [mon1+mon2 for mon1 in mons for mon2 in mons]
        return mons
    
    def get_monomials():
        monss = []
        for x in range(9):
            mons = index_to_mons(x)
            mons = square_mons(mons)
            monss.append(mons)
        return monss
    
    monss = get_monomials()
    ls = [len(mons) for mons in monss]
    
    def zero_list(length):
        return [0 for _ in range(length)]
    
    def get_rows(sample):
        R = sample[0]
        T = sample[1]
        RT = sample[2]
        rows = []
        for x in range(1,9):
            betweenzeros = sum([ls[it] for it in range(x-1)])
            postzeros = sum([ls[it] for it in range(x+1,9)])
                
            row = ([RT[x]*R[i]*R[j]*T[m]*T[n] for (i,j,m,n) in monss[0]]
                   + zero_list(betweenzeros)
                   + [-RT[0]*R[i]*R[j]*T[m]*T[n] for (i,j,m,n) in monss[x]]
                   + zero_list(postzeros)
                  )
    
            rows.append(row)
    
        return rows
        
    M = []
    for s in range(18):
        try:
            sample = get_sample()
        except:
            s -= 1
            continue
        rows = get_rows(sample)
        M += rows
        
    M = matrix(Fp, M)
    
    K = M.right_kernel()
    
    b0 = K.basis()[0]
    
    assert K.dimension() == 1
    
    B = Phi.codomain()
    
    ts = Phi(odd_point)
    hs = B._h
    ds = B._d

    ## ts are the coordinates (0:t1:...:t8) of an odd two torsion point on B
    ## b0 contains the coefficients of the biquadratic monomials appearing in the addition formulae
    
    return ts,b0[:16]

### Interpolating using monomials of degree d in the t_i

d = 2

idxs = list(combinations_with_replacement(range(4), d))

ls = len(idxs) # total number of monomials

def zero_list(length):
    return [0 for _ in range(length)]

def get_interpolation_matrix(s, index_list):
    # s: total number of samples
    # index_list: (indices of) the coefficients to be interpolated
    
    mat = []
    
    for ctr in range(s):

        try:
            sample = get_meta_sample() # Can fail in rare cases
        except:
            ctr -= 1
            continue
        
        ts, cs = sample
        ts = [ts[1], ts[3], ts[4], ts[5]]
        
        monomials = [prod(ts[i] for i in idx) for idx in idxs]
    
        zeros = 0
        
        for index in index_list:
            row = (
                    [cs[index] * m for m in monomials]
                    + zero_list(ls * zeros)
                    + [-cs[1] * m for m in monomials]
                    + zero_list(ls * (len(index_list) - 1 - zeros))
                )
            zeros += 1
            mat.append(row)
        
    return mat

index_list = [2,3,4,6,7,8,9,11,12,13,14]

mat = get_interpolation_matrix(ls+2, index_list)

M = matrix(Fp, mat)

K = M.right_kernel()

assert K.dimension() == 1

the_holy_basis_vector = K.basis()[0]

### Convert into monomials

R.<t1,t3,t4,t5> = Fp[]

vars = [t1,t3,t4,t5]

mon_list = [prod(vars[i] for i in idx) for idx in idxs]

vec_mon = vector(R, mon_list)

extended_index_list = [1] + index_list

for i in range(len(extended_index_list)):
    vec = vector(Fp, the_holy_basis_vector[i*ls : (i+1)*ls])
    print(f"c{extended_index_list[i]} = {vec.inner_product(vec_mon)}")
