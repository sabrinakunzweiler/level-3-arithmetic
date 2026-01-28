r"""
Abelian surfaces in Hesse form
==========================================================================

In this module, we implement basic functionality for
p.p. abelian surfaces in Hesse form.
A reference is our preprint

.. [DecruKunzweiler26] T. Decru and S. Kunzweiler, Abelian surfaces in Hesse form
and explicit isogeny formulas

In particular, our implementation can be used to construct such surfaces,
either from a product of elliptic curves (in Hesse form), or by specifying
the defining equations.

Furthermore, one can construct different models of the Kummer surface.


AUTHORS:

- Sabrina Kunzweiler (2026): initial version

"""

import sys
sys.path.append(".")

from sage.schemes.generic.morphism import SchemeMorphism
from sage.structure.element import AdditiveGroupElement
#import sage.schemes.projective.projective_space as projective_space
from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.schemes.projective.projective_point import SchemeMorphism_point_projective_ring
from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
from sage.structure.element import RingElement
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.schemes.projective.projective_subscheme import AlgebraicScheme_subscheme_projective

from hessian_arithmetic_dim1 import EllipticCurveHessianForm


class AbelianSurfaceHessianForm(AlgebraicScheme_subscheme_projective):
    r"""
    Abelian surface in Hessian form.

    """

    def __init__(self, args, omega=None, OO=None, check=True):
        r"""
        Construct an abelian surface in Hessian form


        INPUT:

        - either args = [d,h] with
            - ``d`` -- tuple containing the coefficients (d0 : ... : d4)
            - ``h`` -- tuple containing the coefficients (h0 : ... : h4)
        - or args =[E1,E2] where E1 and E2 are elliptic curves in Hessian form

        EXAMPLES::

            sage: p = 4*3**3 - 1
            sage: Fp = GF(p**2)
            sage: R.<x> = Fp[]
            sage: omega = (x**2+x+1).roots()[0][0]

        We construct a product surface in Hessian form::

            sage: E0 = EllipticCurve(Fp, [1,0])
            sage: H0 = EllipticCurveHessianForm(E0, omega=omega)
            sage: P0 = E0.lift_x(2)
            sage: E1 = E0.isogeny(P0).codomain()
            sage: H1 = EllipticCurveHessianForm(E1, omega=omega)
            sage: A = AbelianSurfaceHessianForm([H0,H1]); A
            Abelian surface in Hessian form with coefficients d = (91*z2 + 12, 29*z2 + 93, 29*z2 + 93, 1, 1), h =  (0, 0, 0, 106, 1) over Finite Field in z2 of size 107^2
        """
        assert len(args) == 2

        # if the input are elliptic curves, we construct the product
        if isinstance(args[0], EllipticCurveHessianForm):
            self._reducible = True
            E1, E2 = args
            self._ellitpic_curves = (E1, E2)
            K = E1._base_ring
            assert E1._a == K.one()
            assert E2._a == K.one()
            dE1 = E1._d
            dE2 = E2._d
            self._d = dE1*dE2, dE1, dE2, 1, 1
            self._h = K.zero(), K.zero(), K.zero(), -K.one(), K.one()
            OO = [K.zero(),K.zero(),K.zero(),K.zero(),K.one(),-K.one(),K.zero(),-K.one(),K.one()]
            try:
                omega = E1._omega
            except:
                pass
        else:
            self._d = args[0]
            self._h = args[1]
            K = self._d[0].parent()
        d0,d1,d2,d3,d4 = self._d
        h0,h1,h2,h3,h4 = self._h
        #check that d and h are valid inputs
        assert d0*h0 + d1*h1 + d2*h2 + d3*h3 + d4*h4 == 0
        assert h0*(h0**3 + h1**3 + h2**3 + h3**3 + h4**3) + 3*h1*h2*h3*h4 == 0 # h is a point on the burkhardt quartic

        self._base_ring = K
        P8, vars = ProjectiveSpace(8, K, names="X00,X01,X02,X10,X11,X12,X20,X21,X22").objgens()
        X00,X01,X02,X10,X11,X12,X20,X21,X22 = vars
        cubics = [
        d1 * (X00**3 + X01**3 + X02**3 + X10**3 + X11**3 + X12**3 + X20**3 + X21**3 + X22**3) - 3*d0 * (X00*X01*X02 + X10*X11*X12 + X20*X21*X22),
        d2 * (X00**3 + X01**3 + X02**3 + X10**3 + X11**3 + X12**3 + X20**3 + X21**3 + X22**3) - 3*d0 * (X00*X10*X20 + X01*X11*X21 + X02*X12*X22),
        d3 * (X00**3 + X01**3 + X02**3 + X10**3 + X11**3 + X12**3 + X20**3 + X21**3 + X22**3) - 3*d0 * (X01*X12*X20 + X02*X10*X21 + X00*X11*X22),
        d4 * (X00**3 + X01**3 + X02**3 + X10**3 + X11**3 + X12**3 + X20**3 + X21**3 + X22**3) - 3*d0 * (X02*X11*X20 + X00*X12*X21 + X01*X10*X22),
        ]
        self._cubics = cubics
        quadratics = [
            h0*X00**2 + h1*X01*X02 + h2*X10*X20 + h4*X12*X21 + h3*X11*X22,
            h1*X00*X01 + h0*X02**2 + h4*X11*X20 + h3*X10*X21 + h2*X12*X22,
            h0*X01**2 + h1*X00*X02 + h3*X12*X20 + h2*X11*X21 + h4*X10*X22,
            h2*X00*X10 + h4*X02*X11 + h3*X01*X12 + h0*X20**2 + h1*X21*X22,
            h4*X01*X10 + h3*X00*X11 + h2*X02*X12 + h1*X20*X21 + h0*X22**2,
            h3*X02*X10 + h2*X01*X11 + h4*X00*X12 + h0*X21**2 + h1*X20*X22,
            h0*X10**2 + h1*X11*X12 + h2*X00*X20 + h3*X02*X21 + h4*X01*X22,
            h1*X10*X11 + h0*X12**2 + h3*X01*X20 + h4*X00*X21 + h2*X02*X22,
            h0*X11**2 + h1*X10*X12 + h4*X02*X20 + h2*X01*X21 + h3*X00*X22,
        ]
        self._quadratics = quadratics
        self._equations = cubics + quadratics
        if omega:
            self._omega = omega

        #need to set the neutral element
        if OO:
            self._neutral_element = AbelianSurfaceHessianPoint(self, OO, check=check)
        else:
            pass

        AlgebraicScheme_subscheme_projective.__init__(self, P8, cubics+quadratics)


    def _repr_(self):
        """
        String representation.
        """
        s = "Abelian surface in Hessian form with coefficients "
        s += "d = " + str(self._d)
        s += ", h =  " + str(self._h)
        s += " over " + str(self._base_ring)
        return s

    def _set_omega(self, omega):
        """
        A canonical choice of third root of unity is set.

        This is necessary for some applications, such as cubing.
        It is often already set in the beginning.
        """
        self._omega = omega

    def _segre(self, P1, P2):
        """
        Return the segre embedding of the elliptic curve points P1,P2
        """
        x1,y1,z1 = P1._coords
        x2,y2,z2 = P2._coords
        return x1*x2, x1*y2, x1*z2, y1*x2, y1*y2, y1*z2, z1*x2, z1*y2, z1*z2

    def __call__(self, coords, check=True):
        r"""
        Create a point on self from the coordinates.

        If coords consists of two elliptic curve points, the Segre embedding is computed.
        """
        if len(coords) == 2:
            coords = self._segre(*coords) # point on the product
        return AbelianSurfaceHessianPoint(self, coords, check=check)

    def zero(self):
        """
        Return the neutral element of self.

        NOTE : TODO
        """
        return self._neutral_element

    def is_reducible(self):
        """
        Return `True` if self is the product of two elliptic curves.
        """
        try:
            return self._reducible
        except:
            # check if h is a singular point on the Burkhardt quartic
            h0,h1,h2,h3,h4 = self._h
            gradient = [4*h0**3 + h1**3 + h2**3 + h3**3 + h4**3,
            3*h0*h1**2 + 3*h2*h3*h4,
            3*h0*h2**2 + 3*h1*h3*h4,
            3*h0*h3**2 + 3*h1*h2*h4,
            3*h1*h2*h3 + 3*h0*h4**2]
            self._reducible = all([g == 0 for g in gradient])
            return self._reducible

    def elliptic_curves(self):
        """
        If `self` is a product of elliptic curves E1 x E2, return these elliptic curves.
        """
        try:
            return self._ellitpic_curves
        except:
            if not self.is_reducible():
                raise ValueError("The abelian surface is not reducible.")
            d = self._d
            if d[3] != d[4]:
                raise NotImplementedError("We require that the abelian surface is equipped with the product theta structure")
            d1 = d[1]/d[4]
            d2 = d[2]/d[4]
            assert d1*d2 == d[0]/d[4]

            H1 = EllipticCurveHessianForm(d1)
            H2 = EllipticCurveHessianForm(d2)

            self._ellitpic_curves = (H1,H2)
            return (H1,H2)


    def is_irreducible(self):
        """
        Return `True` is self is irreducible.
        """
        return not self.is_reducible()

    def kummer_odd(self):
        """
        Return the odd Kummer surface of self.
        """
        return HessianOddKummerSurface(self)

    def kummer_even(self):
        """
        Return the even Kummer surface of self.
        """
        return HessianEvenKummerSurface(self)

    def canonical_isogeny(self, R1, R2, auxP=None):
        """
        Create the canonical (3,3)-isogeny with kernel 3*(R1,R2).

        If the codomain is reducible, and auxiliary point auxP
        is required to determine the equations
        """
        from hessian_morphisms_dim2 import AbelianSurfaceHessianFormHom

        self._phi = AbelianSurfaceHessianFormHom(self, [R1,R2], "isogeny", auxP=auxP)
        return self._phi

    def symplectic_transformation(self, a,b,c):
        """
        Compute the symplectic transformation which sends
        The kernel defined by <Q1 + a*P1 + b*P2, Q2 + b*P1 + c*P2>
        to canonical form (Q1',Q2').
        """
        from hessian_morphisms_dim2 import AbelianSurfaceHessianFormHom
        omega = self._omega

        #scalars = (omega**(a+c), omega**c, omega**a, omega**(2*b), omega**b)
        scalars = (1 , omega**(2*a), omega**(2*c), omega**(2*a+b+2*c), omega**(2*a+2*b+2*c) )

        return AbelianSurfaceHessianFormHom(self, scalars, "scaling", check=True)

    def DFT(self):
        """
        Compute the symplectic transformation defined by the DFT transform
        """
        from hessian_morphisms_dim2 import AbelianSurfaceHessianFormHom

        return AbelianSurfaceHessianFormHom(self, [], "DFT")

    def negation(self):
        """
        Define the multiplication by -1 map on self.
        """
        from hessian_morphisms_dim2 import AbelianSurfaceHessianFormHom

        return AbelianSurfaceHessianFormHom(self, [], "negation")

    def product_structure_transformation(self):
        """
        If self is reducible, then a transformation to product structure is computed.

        NOTE: This is not necessarily the "easiest" transformation that exists.
        """
        from hessian_morphisms_dim2 import AbelianSurfaceHessianFormCompositeHom

        if not self.is_reducible():
            raise ValueError("The abelian surface is not reducible")

        A = self
        h = A._h
        omega = self._omega
        trafos = []
        #first we reduce to singularities of Type (b)
        if not all([hi!=0 for hi in h]):
            # we need that h is not of the form [0,0,0,-1,1] (or a permutation)
            if sum(h) == 0:
                if h[1] !=0:
                    a,b,c = 1,1,0
                else:
                    a,b,c = 0,1,0
                trafo = A.symplectic_transformation(a,b,c)
                A = trafo.codomain()
                h = A._h
                assert sum(h) != 0
                trafos.append(trafo)
            trafo = A.DFT()
            A = trafo.codomain()
            h = A._h
            assert all([hi!=0 for hi in h])
            trafos.append(trafo)
        #any singularity of type (b) can be transformed to [1,-1,-1,-om^2,-om]
        if h[0] + h[1] == 0:
            a = 0
        elif h[0] + omega*h[1] == 0:
            a = 2
        else:
            a = 1
        if h[0] + h[2] == 0:
            c = 0
        elif h[0] + omega*h[2] == 0:
            c = 2
        else:
            c = 1
        if h[0] + omega**(2*a+2*c+1)*h[3] == 0:
            b = 0
        elif h[0] + omega**(2*a+2*c+2)*h[3] == 0:
            b = 1
        else:
            b = 2
        trafo = A.symplectic_transformation(a,b,c)
        A = trafo.codomain()
        h = A._h
        assert h[0] + h[1] == 0
        assert h[0] + h[2] == 0
        assert h[0] + omega*h[3] == 0
        assert h[0] + omega**2*h[4] == 0
        trafos.append(trafo)
        #
        trafo = A.DFT()
        A = trafo.codomain()
        h = A._h
        assert h[3] + omega*h[4] == 0
        assert h[0] == 0
        trafos.append(trafo)
        #
        trafo = A.symplectic_transformation(0,1,0)
        A = trafo.codomain()
        h = A._h
        d = A._d
        assert d[3] == d[4] #sanity check
        trafos.append(trafo)
        return AbelianSurfaceHessianFormCompositeHom(trafos)


class AbelianSurfaceHessianPoint(SageObject):
    r"""
    Class for representing points on an Abelian surface in
    Hessian form.


    EXAMPLES::
    """

    def __init__(self, parent, coords, check=True):
        r"""
        Constructs the point P = (x00 : ... : x22) on the abelian surface
        in  Hessian form.
        """
        K = parent._base_ring
        self.__base_ring = K
        self._parent = parent


        if check:
            assert all([eq(coords) == 0 for eq in parent._equations])
            self._check = True
        else:
            self._check = False

        self._x00 = K(coords[0])
        self._x01 = K(coords[1])
        self._x02 = K(coords[2])
        self._x10 = K(coords[3])
        self._x11 = K(coords[4])
        self._x12 = K(coords[5])
        self._x20 = K(coords[6])
        self._x21 = K(coords[7])
        self._x22 = K(coords[8])

        self._coords = tuple([K(c) for c in coords])


    def _repr_(self):
        """
        String representation.
        """
        s = "(%s" % self._x00
        s += " : %s" % self._x01
        s += " : %s" % self._x02
        s += " : %s" % self._x10
        s += " : %s" % self._x11
        s += " : %s" % self._x12
        s += " : %s" % self._x20
        s += " : %s" % self._x21
        s += " : %s)" % self._x22
        if not self._check:
            s += "  auxiliary point"
        return s

    def __getitem__(self, n):
        """
        Return the n'th coordinate of this point.
        """
        return self._coords[n]

    def coordinates(self):
        """
        Return coordinates as tuple.
        """
        return self._coords

    def __eq__(self,other):
        """
        Check projective equality of points.
        """
        P8 = self._parent.ambient_space()
        P = P8(self._coords)
        Q = P8(other._coords)
        return P == Q

    def negate(self):
        """
        Return `(-1)*self`.
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        return self._parent([x0, x2, x1, x6, x8, x7, x3, x5, x4])

    def _cubing(self):
        """
        On input `self = (x00 : ... : x22)`, output `(x00**3 : ... : x22**3)`.

        COST:
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        return self._parent([x0**3,x1**3,x2**3,x3**3,x4**3,x5**3,x6**3,x7**3,x8**3], check=False)

    def _DFT(self):
        """
        Compute the DFT transform of the point.

        TODO: adapt to twisted case

        COST: 0
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        try:
            omega = self._parent._omega
        except:
            K = self._parent._base_ring
            R = PolynomialRing(K,"x")
            x = R.gen()
            try:
                f = x**2+x+1
                omega = f.roots(multiplicities=False)[0]
                self._parent._set_omega(omega)
                print("The cube root of unity is set to omega = ", omega)
            except:
                raise ValueError("The base field does not contain a cube root of unity.")
        y0 = x0 + x1          + x2          + x3          + x4          + x5          + x6          + x7          + x8
        y1 = x0 + omega*x1    + omega**2*x2 + x3          + omega*x4    + omega**2*x5 + x6          + omega*x7    + omega**2*x8
        y2 = x0 + omega**2*x1 + omega*x2    + x3          + omega**2*x4 + omega*x5    + x6          + omega**2*x7 + omega*x8
        y3 = x0 + x1          + x2          + omega*x3    + omega*x4    + omega*x5    + omega**2*x6 + omega**2*x7 + omega**2*x8
        y4 = x0 + omega*x1    + omega**2*x2 + omega*x3    + omega**2*x4 + x5          + omega**2*x6 + x7          + omega*x8
        y5 = x0 + omega**2*x1 + omega*x2    + omega*x3    + x4          + omega**2*x5 + omega**2*x6 + omega*x7    + x8
        y6 = x0 + x1          + x2          + omega**2*x3 + omega**2*x4 + omega**2*x5 + omega*x6    + omega*x7    + omega*x8
        y7 = x0 + omega*x1    + omega**2*x2 + omega**2*x3 + x4          + omega*x5    + omega*x6    + omega**2*x7 + x8
        y8 = x0 + omega**2*x1 + omega*x2    + omega**2*x3 + omega*x4    + x5          + omega*x6    + x7          + omega**2*x8

        return self._parent([y0,y1,y2,y3,y4,y5,y6,y7,y8], check=False)

    def _scale(self, c):
        """
            Given `self = (x00 : ... : x11)`, and a scaling vector
            (c0, ...,c4) output `(c0 * x00 : ... : c3 * x22)`

            COST: 9 M
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        c0, c1, c2, c3, c4 = c
        y0 = c0*x0
        y1 = c1*x1
        y2 = c1*x2
        y3 = c2*x3
        y4 = c3*x4
        y5 = c4*x5
        y6 = c2*x6
        y7 = c4*x7
        y8 = c3*x8

        return self._parent([y0,y1,y2,y3,y4,y5,y6,y7,y8], check=False)


    def _compute_d(self):
        """
        Compute the domain coefficients d0, ..., d4 given a point on the surface.

        INPUT:
            - arbitrary point P (if the surface is reducible, then P cannot be 3-torsion)

        OUTPUT:
            d0, ..., d4 defining the cubic equations.
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords

        d0 = x0**3 + x1**3 + x2**3 + x3**3 + x4**3 + x5**3 + x6**3 + x7**3 + x8**3
        d1 = 3*(x0*x1*x2 + x3*x4*x5 + x6*x7*x8)
        d2 = 3*(x0*x3*x6 + x1*x4*x7 + x2*x5*x8)
        d3 = 3*(x0*x4*x8 + x1*x5*x6 + x2*x3*x7)
        d4 = 3*(x0*x5*x7 + x1*x3*x8 + x2*x4*x6)

        assert d0 != 0

        return d0,d1,d2,d3,d4

    def _compute_h(self):
        """
        Compute the domain coefficients h0, ..., h4 given a point on the surface.

        INPUT:
            - arbitrary point P (not 3-torsion)

        OUTPUT:
            h0, ..., h4 defining the quadratic equations.
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords

        A = Matrix([
            [x0**2, x1*x2, x3*x6, x4*x8, x5*x7],
            [x1**2, x0*x2, x4*x7, x5*x6, x3*x8],
            [x2**2, x0*x1, x5*x8, x3*x7, x4*x6],
            [x3**2, x4*x5, x0*x6, x2*x7, x1*x8],
            [x4**2, x3*x5, x1*x7, x0*x8, x2*x6],
            [x5**2, x3*x4, x2*x8, x1*x6, x0*x7],
            [x6**2, x7*x8, x0*x3, x1*x5, x2*x4],
            [x7**2, x6*x8, x1*x4, x2*x3, x0*x5],
            [x8**2, x6*x7, x2*x5, x0*x4, x1*x3]
        ])

        return tuple(A.right_kernel().gen())


    def evaluate_phi(self):
        """
            Evaluate the (3,3)-isogeny with kernel K_2 at a point.
        """
        try:
            phi = self._phi
        except:
            raise ValueError("The 3-isogeny has not yet been created")
        return phi(self)


    def triple(self):
        """
        Compute `3*self`.

        NOTE: Tripling as computed as a composition of 3-isogenies.

        COST:
        """
        try:
            phi = self._parent._phi
        except:
            raise ValueError("The 3-isogeny has not yet been created")
        try:
            phi_dual = phi._dual
        except:
            phi_dual = phi.dual() #phi dual can also be computed from phi

        P = phi(self)
        P = phi_dual(P)
        return P

    def _add_P1(self):
        """
        Add P1 to  `self`, where P1 is the 3-torsion point in the
        canonical symplectic basis (P1,P2,Q1,Q2) of A[3].

        Note: this corresponds to the action of the permutation
        (0,1,2)(3,4,5)(6,7,8)
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        parent = self._parent
        return parent([x1,x2,x0,x4,x5,x3,x7,x8,x6])

    def _add_P2(self):
        """
        Add P2 to  `self`, where P2 is the 3-torsion point in the
        canonical symplectic basis (P1,P2,Q1,Q2) of A[3].

        Note: this corresponds to the action of the permutation
        (0,3,6)(1,4,7)(2,5,8)
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        parent = self._parent
        return parent([x3,x4,x5,x6,x7,x8,x0,x1,x2])

    def _add_Q1(self):
        """
        Add Q1 to  `self`, where Q1 is the 3-torsion point in the
        canonical symplectic basis (P1,P2,Q1,Q2) of A[3].

        Note: this corresponds to scaling by third roots of unity
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        parent = self._parent
        omega = parent._omega
        return parent([x0,omega*x1, omega**2*x2, x3, omega*x4, omega**2*x5, x6, omega*x7, omega**2*x8])

    def _add_Q2(self):
        """
        Add Q2 to  `self`, where Q2 is the 3-torsion point in the
        canonical symplectic basis (P1,P2,Q1,Q2) of A[3].

        Note: this corresponds to scaling by third roots of unity
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = self._coords
        parent = self._parent
        omega = parent._omega
        return parent([x0,x1,x2,omega*x3,omega*x4,omega*x5,omega**2*x6,omega**2*x7,omega**2*x8])


class HessianEvenKummerSurface(SageObject):
    r"""
    The even model in PP**4 of the Kummer surface of an abelian
    surface in Hessian form.

    EXAMPLES::


    """
    def __init__(self, hessian_surface):
        r"""
        Constructor for the even model Kummer surface from an abelian surface in Hessian form.
        """
        self._hessian_form = hessian_surface
        self._base_ring = hessian_surface.base_ring()
        self._d = hessian_surface._d
        self._h = hessian_surface._h
        self._isogeny_neighbour = None

        P4 = ProjectiveSpace(4, self._base_ring,"U0,U1,U2,U3,U4")
        P4.inject_variables()
        self._ambient_space = P4
        h0,h1,h2,h3,h4 = self._h
        self._quadric = U0*(h0**2*U0 + h1**2*U1 + h2**2*U2 + h3**2*U3 + h4**2*U4) + 2*h0*(h1*U1**2 + h2*U2**2 + h3*U3**2 + h4*U4**2) +  2*((h3*h4)*U1*U2 + (h2*h4)*U1*U3 + (h1*h4)*U2*U3 + (h2*h3)*U1*U4 + (h1*h3)*U2*U4 + (h1*h2)*U3*U4)
        self._cubic = None #TODO: compute the equation for the cubic equation


    def __repr__(self):
        r"""
        String representation of the Kummer line.
        """
        return f"Even model of the Kummer surface of {self._hessian_form}"

    def __call__(self, coords, check=True):
        r"""
        Create a Kummer point from the coordinates.
        """
        return HessianEvenKummerSurfacePoint(self, coords, check=check)


class HessianEvenKummerSurfacePoint(SageObject):
    r"""
    Class for representing points on the even model of
    a Kummer surface in Hessian form.

    EXAMPLES:


    """

    def __init__(self, parent, coords, check=True):
        r"""
        On input (x00 : ... :x22), construct the point
        P = (x00 : x01 + x02 : x10 + x20 : x11 + x22 : x12 + x21)
        on the Kummer surface.

        Alternatively, the input can directly be a tuple
        (u0 : ... : u4) representing a point on the Kummer surface.
        """
        if isinstance(coords, AbelianSurfaceHessianPoint):
            coords = coords._coords
        K = parent._base_ring
        self.__base_ring = K

        self._parent = parent

        if len(coords) == 9:
            x00, x01, x02, x10, x11, x12, x20, x21, x22 = coords
            u0 = x00
            u1 = x01 + x02
            u2 = x10 + x20
            u3 = x11 + x22
            u4 = x12 + x21

        if len(coords) == 5:
            u0, u1, u2, u3, u4 = coords

        if check:
            assert parent._quadric(u0,u1,u2,u3,u4) == 0
            assert True #TODO: check that the cubic equation vanishes
        self._coords = (u0,u1,u2,u3,u4)


    def _repr_(self):
        """
        String representation.
        """
        s = "(%s" % self._coords[0]
        s += " : %s" % self._coords[1]
        s += " : %s" % self._coords[2]
        s += " : %s" % self._coords[3]
        s += " : %s)" % self._coords[4]
        return s

    def coordinates(self):
        return self._coords

    def __eq__(self,other):
        P4 = self._parent._ambient_space
        P = P4(self._coords)
        Q = P4(other._coords)
        return P == Q

    def _cubing(self):
        """
        On input (u0 : ... : u4),
        compute (x00**3 :  ... : x12**3 + x21**3).

        TODO

        COST:
        """
        pass

    def _DFT(self):
        """
        Given x, u, output x + u, 2*x - u

        COST: 0
        """
        u0,u1,u2,u3,u4 = self._coords

        y0 = u0 + 2*u1 + 2*u2 + 2*u3 + 2*u4
        y1 = u0 - u1 + 2*u2 - u3 - u4
        y2 = u0 + 2*u1 - u2 - u3 - u4
        y3 = u0 - u1 - u2 - u3 + 2*u4
        y4 = u0 - u1 - u2 + 2*u3 - u4

        #Note: technically, the point is no longer on the same Kummer surface
        self._parent([y0,y1,y2,y3,y4], check=False)

    def _scale(self, c):
        """
            Given `self = (u0 : ... : u4)` and `c = (c0 : ... : c4)`,
            output `(c0 * u0 : ... : c4 * u4)`

            COST: 5 M
        """
        u0,u1,u2,u3,u4 = self._coords
        c0,c1,c2,c3,c4 = c

        uc0 = u0*c0
        uc1 = u1*c1
        uc2 = u2*c2
        uc3 = u3*c3
        uc4 = u4*c4

        #Note: technically, the point is no longer on the same Kummer surface
        return self._parent([uc0,uc1,uc2,uc3,uc4], check=False)

    def evaluate_phi_1(self):
        """
            COST:
        """
        pass


    def xTRPL(self):
        """
            Triple the point.

            NOTE: Tripling is computed as a composition of 3-isogenies.

            COST:
        """
        pass


class HessianOddKummerSurface(SageObject):
    r"""
    The odd model in PP**3 of the Kummer surface of an abelian
    surface in Hessian form.

    EXAMPLES::



    """
    def __init__(self, hessian_surface):
        r"""
        Constructor for the even model Kummer surface from an abelian surface in Hessian form.
        """
        self._hessian_form = hessian_surface
        self._base_ring = hessian_surface.base_ring()
        self._d = hessian_surface._d
        self._h = hessian_surface._h
        self._isogeny_neighbour = None

        P3 = ProjectiveSpace(3, self._base_ring, 'V1,V2,V3,V4')
        P3.inject_variables()
        self._ambient_space = P3
        h0,h1,h2,h3,h4 = self._h

        c0 = 4*h0**3 + h1**3 + h2**3 + h3**3 + h4**3
        c1 = h0*h1**2 + h2*h3*h4
        c2 = h0*h2**2 + h1*h3*h4
        c3 = h0*h3**2 + h1*h2*h4
        c4 = h0*h4**2 + h1*h2*h3
        self._defining_equation = c0 * V1*V2*V3*V4 - c1 * V1 * (V2**3 + V3**3 + V4**3) + c2 * V2 * (V1**3 + V3**3 - V4**3) + c3 * V3 * (V1**3 - V2**3 + V4**3) + c4 * V4 * (V1**3 + V2**3 - V3**3)


    def __repr__(self):
        r"""
        String representation of the Kummer line.
        """
        return f"Odd model of the Kummer surface of {self._hessian_form}"

    def __call__(self, coords):
        r"""
        Create a Kummer point from the coordinates.
        """
        return HessianOddKummerSurfacePoint(self, coords)


class HessianOddKummerSurfacePoint(SageObject):
    r"""
    Class for representing points on the odd model of
    a Kummer surface in Hessian form.

    EXAMPLES:


    """

    def __init__(self, parent, coords, check=True):
        r"""
        On input (x00 : ... : x22), construct the point
        P = (x01 - x02 : x10 - x20 : x11 - x22 : x12 - x21)
        on the Kummer surface.

        Alternatively, the input can directly be a tuple
        (v1 : ... : v4) representing a point on the Kummer surface.
        """
        if isinstance(coords, AbelianSurfaceHessianPoint):
            coords = coords._coords
        K = parent._base_ring
        self.__base_ring = K

        self._parent = parent

        if len(coords) == 9:
            x00, x01, x02, x10, x11, x12, x20, x21, x22 = coords
            v1 = x01 - x02
            v2 = x10 - x20
            v3 = x11 - x22
            v4 = x12 - x21

        if len(coords) == 4:
            v1, v2, v3, v4 = coords

        if check:
            assert parent._defining_equation(v1,v2,v3,v4) == 0
            assert True #TODO: check that the cubic equation vanishes
        self._coords = (v1,v2,v3,v4)


    def __repr__(self):
        """
        String representation.
        """
        s = "(%s" % self._coords[0]
        s += " : %s" % self._coords[1]
        s += " : %s" % self._coords[2]
        s += " : %s" % self._coords[3]
        return s

    def coordinates(self):
        return self._coords

    def __eq__(self,other):
        P3 = self._parent._ambient_space
        P = P3(self._coords)
        Q = P3(other._coords)
        return P == Q

    def lift(self, all_solutions=False):
        """
            Lift the point to a point on the abelian surface.
            If `all_solutions=True`, provide both lifts.

            EXAMPLES::
        """
        K = self._parent._base_ring
        A = self._parent._hessian_form
        try:
            u0 = K.one()
            S = PolynomialRing(K, "x0,x1,x2,x3,x4,x5,x6,x7,x8")
            x0,x1,x2,x3,x4,x5,x6,x7,x8 = S.gens()
            h0,h1,h2,h3,h4 = self._parent._h
            v1,v2,v3,v4 = self._coords
            relations = [x1-x2 - v1, x3-x6 - v2, x4-x8 - v3, x5-x7 - v4] #definition of the vi
            equations = self._parent._hessian_form._equations
            I = S.ideal(equations+relations)
            V = I.variety() # note that the above contains many linear relations, and only one square-root computation is necessary.
            if not V:
                return None
            elif all_solutions:
                solutions = []
                for v in V:
                    #x0,x1,x2,x3,x4,x5,x6,x7,x8 = 2*u0, v[u1] + v1, v[u1] - v1, v[u2] + v2, v[u3] + v3, v[u4] + v4, v[u2] - v2, v[u4] - v4, v[u3] - v4
                    x00,x01,x02,x10,x11,x12,x20,x21,x22 = v[x0],v[x1],v[x2],v[x3],v[x4],v[x5],v[x6],v[x7],v[x8]
                    solutions.append(A([x00,x01,x02,x10,x11,x12,x20,x21,x22]))
                return solutions
            else:
                v = V[0]
                xx00,x01,x02,x10,x11,x12,x20,x21,x22 = v[x0],v[x1],v[x2],v[x3],v[x4],v[x5],v[x6],v[x7],v[x8]
                #x0,x1,x2,x3,x4,x5,x6,x7,x8 = 2*u0, v[u1] + v1, v[u1] - v1, v[u2] + v2, v[u3] + v3, v[u4] + v4, v[u2] - v2, v[u4] - v4, v[u3] - v4
                solution = A([x00,x01,x02,x10,x11,x12,x20,x21,x22])
                return solution
        except:
            raise NotImplementedError("seems to be an exceptional case")


    def _cubing(self):
        """
        On input (v1 : ... : v4),
        compute (x01**3 - x02**3 :  ... : x12**3 - x21**3).

        TODO

        COST:
        """
        pass

    def _DFT(self):
        """
        Given x, u, output x + u, 2*x - u

        COST: 0
        """
        v1,v2,v3,v4 = self._coords

        y1 =  v1 + v3 - v4
        y2 =  v2 + v3 + v4
        y3 =  v1 + v2 - v3
        y4 = -v1 + v2 - v4

        #Note: technically, the point is no longer on the same Kummer surface
        self._parent([y1,y2,y3,y4], check=False)

    def _scale(self, c):
        """
            Given `self = (u0 : ... : u4)` and `c = (c0 : ... : c4)`,
            output `(c0 * u0 : ... : c4 * u4)`

            COST: 5 M
        """
        u1,u2,u3,u4 = self._coords
        if len(c) == 4:
            c1,c2,c3,c4 = c
        elif len(c) == 5:
            _,c1,c2,c3,c4 = c

        vc1 = v1*c1
        vc2 = v2*c2
        vc3 = v3*c3
        vc4 = v4*c4

        #Note: technically, the point is no longer on the same Kummer surface
        return self._parent([vc1,vc2,vc3,vc4], check=False)

    def evaluate_phi(self):
        """
            COST:
        """
        pass


    def TRPL(self):
        """
            Triple the point.

            NOTE: Tripling is computed as a composition of 3-isogenies.

            COST:
        """
        pass