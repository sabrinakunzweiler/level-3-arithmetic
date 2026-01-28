r"""
3^n-isogeny computations
==========================================================================

Here, we provide an algorithm to compute 3^n-isogenies
between p.p. abelian surfaces in Hesse form.
This is based on the modules `hessian_arithmetic_dim1`
and `hessian_arithmetic_dim2`.


AUTHORS:

- Sabrina Kunzweiler (2026): initial version

"""

from hessian_arithmetic_dim1 import *
from hessian_arithmetic_dim2 import *
from hessian_morphisms_dim2 import *


def create_basis(E1,E2,k,omega=None):
	"""
	Construct a symplectic basis of (E1 x E2)[3^k].

	INPUT:
	- E1,E2: elliptic curves with full rational 3^k-torsion,
	- omega (optional) third root of unity

	OUTPUT:
	- (P1,P2,Q1,Q2) with E1[3^k] = <P1,Q1>, E2[3^k] = <P2,Q2>
	with e(P1,Q1) = e(P2,Q2), and e(3^(k-1)P1,3^(k-1)Q1) = omega
	(if omega is specified)
	"""
	P1,Q1 = E1.torsion_basis(3^k)
	P1_3 = 3**(k-1)*P1
	Q1_3 = 3**(k-1)*Q1

	if omega:
		if P1_3.weil_pairing(Q1_3,3) != omega^2:
			Q1 = 2*Q1
			Q1_3 = 2*Q1_3
	else:
		omega = P1_3.weil_pairing(Q1_3,3)^2
	a1 = P1.weil_pairing(Q1,3^k)

	P2,Q2 = E2.torsion_basis(3^k)
	a2 = P2.weil_pairing(Q2,3^k)
	d = a1.log(a2)
	Q2 = d*Q2
	# sanity check
	assert P2.weil_pairing(Q2,3^k) == a1
	return (P1,P2,Q1,Q2)

def translate_to_Hessian(basis,k, kernel_scalars):
	"""
	Given a symplectic basis for (E1 x E2)[3^k],
	and scalars defining a (3^k,3^k)- isogeny,
	output the kernel generators in Hessian form.

	INPUT:
	- basis = (P1,P2,Q1,Q2), where E1[3^k] = <P1,Q1>, E2[3^k] = <P2,Q2>
	- kernel_scalars = (a,b,c) with a,b,c in ZZ

	OUTPUT:
	- Points R,S in A[3^k], where A is the Hessian form of E1 x E2,
	  and R1,R2 generate <(P1 + c*Q1, b*Q2),(b*Q1, P2 + a*Q2)>
	- Points R' =3^(k-2)*R, S' = 3^(k-2)*S: auxiliary 9-torsion points
	"""

	# create the Hessian
	P1,P2,Q1,Q2 = basis

	P1_3 = 3^(k-1)*P1
	Q1_3 = 3^(k-1)*Q1
	P2_3 = 3^(k-1)*P2
	Q2_3 = 3^(k-1)*Q2

	omega = P1_3.weil_pairing(Q1_3,3)^2

	H1 = EllipticCurveHessianForm(E1, basis=[P1_3,Q1_3])
	H2 = EllipticCurveHessianForm(E2, basis=[P2_3,Q2_3])
	A0 = AbelianSurfaceHessianForm([H2,H1], omega=omega^2)

	a,b,c = kernel_scalars

	R1 = H1.map_point(P1+a*Q1)
	R2 = H2.map_point(b*Q2)
	S1 = H1.map_point(b*Q1)
	S2 = H2.map_point(P2+c*Q2)

	#auxiliary 9 -torsion points
	R1_9 = H1.map_point(3^(k-2)*(P1+a*Q1))
	R2_9 = H2.map_point(3^(k-2)*(b*Q2))
	S1_9 = H1.map_point(3^(k-2)*(b*Q1))
	S2_9 = H2.map_point(3^(k-2)*(P2+c*Q2))


	R = A0([R2,R1])
	S = A0([S2,S1])
	R_9 = A0([R2_9,R1_9])
	S_9 = A0([S2_9,S1_9])

	return (R,S), (R_9,S_9)

def compute_isogeny_chain(kernel, kernel_aux, n, scalars, auxP=None):
	"""
	Compute the (3^n,3^n)-isogeny chain with the given kernel `3*kernel`.

	INPUT:
	- kernel = (P,Q): generators of an isotropic (3^(n+1),3^(n+1))-group
	- aux_kernel: 9-torsion points lying above the kernel generators
	- k: exponent
	- scalars = (a,b,c): the kernel generators are of the form (P1 + aQ1 + bQ2, P2 + bQ1 + cQ2)
	- optional: if one expects to encounter a reducible surface in the chain,
	an auxiliary point is needed to determine the equations defining the reducible surface
	(for simplicity, we assume that in this case the last step is a splitting)
	"""

	P,Q = kernel
	P_9, Q_9 = kernel_aux
	a,b,c = scalars

	# first step: transform the kernel into the right form
	# (this only depends on a,b,c)
	A0 = P._parent
	trafo0 = A0.symplectic_transformation(a,b,c)
	P,Q = trafo0(P), trafo0(Q)
	P_9,Q_9 = trafo0(P_9), trafo0(Q_9)

	m1 = trafo0.codomain().negation()
	#P,Q,P_9,Q_9 = m1(P), m1(Q), m1(P_9), m1(Q_9)
	maps = [trafo0]

	A = trafo0.codomain()
	for k in range(n):
		# discrete Fourier transform (sending K1 -> K2)
		trafo = A.DFT()
		P,Q = trafo(P), trafo(Q)
		P_9,Q_9 = trafo(P_9), trafo(Q_9)
		maps.append(trafo)
		#negation (technicality)
		m1 = trafo.codomain().negation()
		P,Q,P_9,Q_9 = m1(P), m1(Q), m1(P_9), m1(Q_9)
		maps.append(m1)
		#
		A = m1.codomain()
		if k < n-1:
			#isogeny-computation
			phi = A.canonical_isogeny(P_9, Q_9)
			# 9-torsion points (on the codomain of phi, i.e. 27-torsion points on the domain)
			P_9, Q_9 = P,Q
			for i in range(n-k-2):
				P_9 = P_9.triple()
				Q_9 = Q_9.triple()
			P_9, Q_9 = phi(P_9), phi(Q_9)
			P,Q = phi(P), phi(Q) # 3^(n-k) torsion
			A = phi.codomain()
		else:
			if auxP:
				for m in maps:
					auxP = m(auxP)
				phi = A.canonical_isogeny(P_9, Q_9, auxP=auxP)
			else:
				phi = A.canonical_isogeny(P_9,Q_9)
		maps.append(phi)

	return AbelianSurfaceHessianFormCompositeHom(maps)

