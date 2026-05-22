K0.<omega> = QQ.extension(x^2+x+1)
K.<t0,t1,t2,t3,t4> = K0[]
L.<a00,a01,a02,a03,a04,a11,a12,a13,a14,a22,a23,a24,a33,a34,a44,c0,c1,c2,c3,c4,c5,c6,c7,c8> = Frac(K)[]
R.<A0,A1,A2,A3,A4,A5,A6,A7,A8> = Frac(L)[]
aij = [a00,a01,a02,a03,a04,a11,a12,a13,a14,a22,a23,a24,a33,a34,a44]
M_add = Matrix([[a00,a01,a02,a03,a04],[a01,a11,a12,a13,a14],[a02,a12,a22,a23,a24],[a03,a13,a23,a33,a34],[a04,a14,a24,a34,a44]])

M3 = Matrix([[1,1,1],[1,omega,omega^2],[1,omega^2,omega]])
M9 = block_matrix([[M3,M3,M3],[M3,omega*M3,omega^2*M3],[M3,omega^2*M3,omega*M3]])
OO = vector([t0,t1,t1,t2,t3,t4,t2,t4,t3])
AA = vector([A0,A1,A2,A3,A4,A5,A6,A7,A8])
cc = [c0,c1,c2,c3,c4,c5,c6,c7,c8]
om = omega

def vector_form(vec):
    A0, A1, A2, A3, A4, A5, A6, A7, A8 = vec
    VA0 = vector([A0^2, A1*A2, A3*A6, A4*A8, A5*A7])
    VA1 = vector([A1^2, A0*A2, A4*A7, A5*A6, A3*A8])
    VA2 = vector([A2^2, A0*A1, A5*A8, A3*A7, A4*A6])
    VA3 = vector([A3^2, A4*A5, A0*A6, A2*A7, A1*A8])
    VA4 = vector([A4^2, A3*A5, A1*A7, A0*A8, A2*A6])
    VA5 = vector([A5^2, A3*A4, A2*A8, A1*A6, A0*A7])
    VA6 = vector([A6^2, A7*A8, A0*A3, A1*A5, A2*A4])
    VA7 = vector([A7^2, A6*A8, A4*A1, A2*A3, A0*A5])
    VA8 = vector([A8^2, A6*A7, A5*A2, A0*A4, A1*A3])

    return [VA0,VA1,VA2,VA3,VA4,VA5,VA6,VA7,VA8]

def to_equation(left, right, result):
    # takes left, right and result as inputs in P8 and converts them to P5^9
    # then computes left * M_add * right = result as set of equations
    left_vec = vector_form(left)
    right_vec = vector_form(right)
    XX = [left_vec[i]*M_add*right_vec[i] for i in range(9)]

    ## we take instead (Aw)[i] * v[i+1] - (Aw)[i+1] * v[i] for projective factor
    return [ XX[i]*result[i+1] - XX[i+1]*result[i] for i in range(8) ] + [ XX[8]*result[0] - XX[0]*result[8] ] 

## functions for three torsion and negation
def sig1(P):
    return [ P[1], P[2], P[0], P[4], P[5], P[3], P[7], P[8], P[6]]
def sig2(P):
    return [ P[3], P[4], P[5], P[6], P[7], P[8], P[0], P[1], P[2]]
def tau1(P):
    return [ P[0], om*P[1], om*om*P[2], P[3], om*P[4], om*om*P[5], P[6], om*P[7], om*om*P[8]]
def tau2(P):
    return [ P[0], P[1], P[2], om*P[3], om*P[4], om*P[5], om*om*P[6], om*om*P[7], om*om*P[8]]
def neg(vec):
    return [vec[0], vec[2], vec[1], vec[6], vec[8], vec[7], vec[3], vec[5], vec[4]]

## define three torsion points
three_torsion = [ 
    sig1(OO),
    sig2(OO),
    tau1(OO),
    tau2(OO)
]

equations = []

for P in three_torsion:
    # add equations P + P = -P
    equations += to_equation(P, P, neg(P))

MM = Matrix(R, [ eq.coefficients() for eq in equations if eq.monomials() == aij ])

small_eqs = [ eq for eq in equations if eq.monomials() != aij ]