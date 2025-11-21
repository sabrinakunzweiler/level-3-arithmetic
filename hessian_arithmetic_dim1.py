"""
Elliptic curves in (twisted) Hessian form, and their Kummer lines.


Structure for the Kummer line arithmetic follows
https://github.com/nicolassarkis/sage/blob/kummer_line/src/sage/schemes/elliptic_curves/kummer_line.py

"""

from sage.schemes.generic.morphism import SchemeMorphism
from sage.structure.element import AdditiveGroupElement
import sage.schemes.projective.projective_space as projective_space
from sage.schemes.projective.projective_point import SchemeMorphism_point_projective_ring
import sage.schemes.curves.projective_curve as plane_curve
from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
from sage.structure.element import RingElement
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector


#auxiliary function
def transformation_matrix_to_Hessian(P1,P2,P3,omega):
    """
    Return the coordinate transformation to a Hessian form.

    INPUT:
        - points P1, P2, P3, where (P1,P2) is a basis of the
        3-torsion of some elliptic curve E, and P3 = P1 + P2,
        omega = e3(P1,P2), a third root of unity.

    OUTPUT:
        A 3x3 matrix M defining a transformation t: E -> H, P |-> M * P
    """
    assert 3*P1 == 0 and 3*P2 == 0
    assert P1 + P2 == P3

    x1,y1 = P1.xy()
    x2,y2 = P2.xy()
    x3,y3 = P3.xy()

    D = Matrix([[x1,y1,1],[x2,y2,1],[x3,y3,1]])
    delta = D.determinant()
    a1 = - (x1 - x3) * delta
    a3 = omega * (y1 - y3) * (x2 - x3) * (x1 - x2)
    a2 = - a3 + (x1 + (omega - 1)*x2 + (-omega)*x3) * delta
    b1 = 0
    b2 = omega * (x2 - x3) * (x1 - x3) * (x1 - x2)
    b3 = - b2
    c1 = x2 * (x1 - x3) * delta
    c3 = - omega * (x2 - x3) * (x1 - x2) * (x3*y1 - x1*y3)
    c2 = - c3 - (omega*x1*x2 + (-omega + 1)*x1*x3 - x2*x3) * delta

    M = Matrix([[a1,b1,c1],[a2,b2,c2],[a3,b3,c3]])
    return M

class EllipticCurveHessianForm(plane_curve.ProjectivePlaneCurve):
    r"""
    Elliptic curve in Hessian form.

    EXAMPLES:

    We construct a Curve in Hessian form from a given elliptic curve E.
    We require that E has full rational 3-torsion::

        sage: p = 4*3^3 - 1
        sage: Fp = GF(p^2)
        sage: R.<x> = Fp[]
        sage: omega = (x^2+x+1).roots()[0][0]

        sage: E = EllipticCurve(Fp, [1,0])
        sage: H = EllipticCurveHessianForm(E); H # random
        Elliptic Curve in Hessian form defined by x^3 + y^3 + (-z2 + 30)*x*y*z + z^3 over Finite Field in z2 of size 107^2
    
    We can check that the curves are isomorphic, 
    using the formula for the j-invariant on Hessian curves::

        sage: H.j_invariant() == E.j_invariant()
        True

    We can map the points from E to H::

        sage: P1 = E.random_point()
        sage: P2 = E.random_point()
        sage: Q1 = H.map_point(P1)
        sage: Q2 = H.map_point(P2)
    """

    def __init__(self, arg, a=1, omega=None, basis=None, check=False):
        r"""
        Construct an elliptic curve in (twisted) Hessian form
        a*X^3 + Y^3 + Z^3 = 3*d*X*Y*Z
        By default, a=1, i.e. the curve is untwisted.

        INPUT:

        - ``arg`` -- either this is ``d``, the Hessian coefficient of the curve
        (with optional parameter a to define a twist),
        or an ellitpic curve ``E`` with full rational 3-torsion,
        and the transformation into Hessian form is computed on the spot
        """

        if isinstance(arg, RingElement):
            d = arg
            K = d.parent()
            self._base_ring = K
            self._d = arg
            self._a = K(a)
            if omega:
                self._omega = omega
        elif isinstance(arg, EllipticCurve_generic):
            E = arg
            self._elliptic_curve = E
            K = E.base_ring()
            self._base_ring = K
            if basis:
                [P1,P2] = basis
            else:
                [P1,P2] = E.torsion_basis(3)
            P3 = P1 + P2
            omega = P1.weil_pairing(P2, 3)**2
            self._omega = omega
            M = transformation_matrix_to_Hessian(P1,P2,P3,omega)
            self._trafo = M
            #need to check that there exists a point of order >3.
            if E.order() == 9:
                raise ValueError()
            while True:
                P = E.random_point()
                if P.order() != 3 and P.order() != 1:
                    break
            [X,Y,Z] = M * vector(P)
            d =  (X**3 + Y**3 + Z**3)/(3*X*Y*Z)
            self._d = d
            self._a = self._base_ring.one()
        else:
            raise ValueError("The input is not valid")

        PP = projective_space.ProjectiveSpace(2, self._base_ring, names='xyz')
        x, y, z = PP.coordinate_ring().gens()
        F = a*x**3 + y**3 + z**3 - 3*d*x*y*z
        self._equation = F
        self._neutral_element = EllipticCurveHessianPoint(self, [K.zero(),-K.one(),K.one()], check=check)
        plane_curve.ProjectivePlaneCurve.__init__(self, PP, F)

    def _repr_(self):
        """
        String representation.
        """
        s = "Elliptic Curve in Hessian form defined by "
        s += "%s" % self._equation
        s += " over %s" % self.base_ring()
        return s

    def _set_omega(self, omega):
        """
        A canonical choice of third root of unity is set.

        This is necessary for some applications, such as cubing.
        It is often already set in the beginning.
        """
        self._omega = omega

    def __call__(self, coords, check=True):
        r"""
        Create a point on self from the coordinates.
        """
        return EllipticCurveHessianPoint(self, coords, check=check)

    def zero(self):
        """
        Return the neutral element `(0:-1:1)` of the Hessian curve.
        """
        return self._neutral_element

    def map_point(self, P):
        r"""
        Map point from the "base" elliptic curve to the curve in Hessian form.

        NOTE: This only makes sense if self was created from an elliptic curve
        in Weierstrass form.
        """
        if not self._trafo:
            raise NotImplementedError

        M = self._trafo
        x,y,z = M*vector(P)
        return self([x,y,z])

    def j_invariant(self):
        d = self._d
        a = self._a
        j = (3*d*(8*a+d**3)/(d**3-a))**3/a
        return j

    def _special_isogeny_neighbour(self):
        """
        Compute the Kummer line of a (special) 3-isogenous neighbour

        This concerns the 3-isogeny H -> H' with kernel <(0: 1 : omega)>.
        """
        try:
            return self._isogeny_neighbour
        except:
            a1 = self._d**3 - self._a
            d1 = self._d
            omega = self._omega

            E1 = EllipticCurveHessianForm(d1, a=a1, omega=omega)
            self._isogeny_neighbour = E1
            self._a1 = a1
            self._d1 = d1

            return self._isogeny_neighbour

    def kummer(self):
        """
        Return the Kummer line of self.
        """
        return HessianKummerLine(self)

    def untwist(self):
        """
        Return the untwisted Hessian form of `self` if it exists.

        The untwisted form is X^3 + Y^3 + Z^3 = 3d*XYZ.


        EXAMPLES::
            sage: Fp = FiniteField(19)
            sage: E1 = EllipticCurveHessianForm(Fp(2),a=Fp(3))
            sage: E2 = E1.untwist()
            Traceback (most recent call last)
            ...
            ValueError: The curve does not admit a model in untwisted form.

            sage: E1 = EllipticCurveHessianForm(Fp(2),a=Fp(7))
            sage: E2 = E1.untwist(); E2
            Elliptic Curve in Hessian form defined by x^3 + y^3 + 8*x*y*z + z^3 over Finite Field of size 19
            sage: E1.j_invariant() == E2.j_invariant()
            True
        """
        a,d = self._a, self._d
        if a == 1:
            return self
        try:
            alpha = a.nth_root(3)
        except:
            raise ValueError("The curve does not admit a model in untwisted form.")

        return EllipticCurveHessianForm(d/alpha)

    def twisted_normalform(self):
        """
        Return the twisted normal form of `self`.

        The twisted normal form is a*X^3 + Y^3 + Z^3 = 3*XYZ.


        EXAMPLES::
            sage: Fp = FiniteField(19)
            sage: E1 = EllipticCurveHessianForm(Fp(2),a=Fp(3))
            sage: E2 = E1.twisted_normalform(); E2
            sage: E1.j_invariant() == E2.j_invariant()
            True
        """
        a,d = self._a, self._d
        if d == 1:
            return self
        else:
            K = self._base_ring
            return EllipticCurveHessianForm(K.one(), a=a/d**3)

class EllipticCurveHessianPoint(SageObject):
    r"""
    Class for representing points on an elliptic curve in
    Hessian form.

    EXAMPLES::

        sage: p = 37
        sage: Fp = GF(p)
        sage: R.<x> = Fp[]
        sage: omega = (x^2+x+1).roots()[0][0]
        sage: E = EllipticCurve(Fp, [4,1])
        sage: H = EllipticCurveHessianForm(E)

    We can map points from the "base curve E" to H::

        sage: P1 = E([27,16])
        sage: Q1 = H.map_point(P1); Q1
        (26 : 0 : 11)

    Or we can create points directly by passing coordinates::

        sage: R1 = H([10,0,27])
        sage: Q1 == R1
        True
        sage: Q1 == H([Fp(10/27),0,1])
        True

    Arithmetic on H is implemented as well::

        sage: P2 = E([22,9])
        sage: Q2 = H.map_point(P2); Q2
        (27 : 5 : 32)
        sage: Q3 = Q1.add(Q2)
        sage: Q3 == H.map_point(P1 + P2)
        True
        sage: Q4 = Q1.double()
        sage: Q4 == H.map_point(2*P1)
        True
        sage: Q5 = Q1.triple()
        sage: Q5 == H.map_point(3*P1)
        True
    """

    def __init__(self, parent, coords, check=True):
        r"""
        Constructs the point P = (x : y : z) on an elliptic curve
        in  Hessian form.

        Alternatively, the input can directly be a tuple (x, u) representing a curve on the Kummer line.
        """
        K = parent._base_ring
        self._base_ring = K
        self._parent = parent

        if len(coords) == 2: #allow affine input
            coords.append(K.one())

        if check:
            assert parent._equation(coords) == 0
            self._check = True
        else:
            self._check = False

        self._coords = coords
        self._x = K(coords[0])
        self._y = K(coords[1])
        self._z = K(coords[2])

    def _repr_(self):
        """
        String representation.
        """
        s = "(%s " % self._x
        s += ": %s" % self._y
        s += " : %s)" % self._z
        if not self._check:
            s += "  auxiliary point"
        return s

    def xyz(self):
        """
        Return coordinates as tuple.
        """
        return self._x, self._y, self._z

    def __eq__(self,other):
        """
        Check projective equality of points.
        """
        x1, y1, z1 = self.xyz()
        x2, y2, z2 = other.xyz()

        if z1 != 0:
            return x2*z1 == x1*z2 and y2*z1 == y1*z2
        else:
            return z2 == 0 and x1*y2 == y1*x2

    def add(self, other):
        r"""
        Compute the sum of two points P, Q on the Hessian curve self.
        """
        x1,y1,z1 = self.xyz()
        x2,y2,z2 = other.xyz()
        x3 = x1**2*y2*z2 - x2**2*y1*z1
        y3 = z1**2*x2*y2 - z2**2*x1*y1
        z3 = y1**2*x2*z2 - y2**2*x1*z1
        return self._parent([x3,y3,z3])

    def double(self):
        r"""
        Compute `2*self`.

        """
        x1,y1,z1 = self.xyz()
        a = self._parent._a
        x3 = (z1**3 - y1**3)*x1
        y3 = (y1**3 - a*x1**3)*z1
        z3 = (a*x1**3 - z1**3)*y1
        return self._parent([x3,y3,z3])

    def negate(self):
        """
        Return `(-1)*self`.
        """
        x1,y1,z1 = self.xyz()
        return self._parent([x1,z1,y1])

    def _cubing(self):
        """
        On input `self = (x : y : z)`, output `(x^3 : y^3 : z^3)`.

        COST: 3 S + 3 M
        """
        x, y, z = self.xyz()
        x_im = x**3
        y_im = y**3
        z_im = z**3

        return self._parent([x_im,y_im,z_im], check=False)

    def _DFT(self):
        """
        Compute the DFT transform of the point.

        TODO: adapt to twisted case

        COST: 0
        """
        x, y, z = self.xyz()
        try:
            omega = self._parent._omega
        except:
            K = self._base_ring
            R = PolynomialRing(K,1)
            x = R.gen()
            try:
                omega = (x^2+x+1).roots(multiplicties=False)[0]
                self._parent.set_omega(omega)
                print("The cube root of unity is set to omega = ", omega)
            except:
                raise ValueError("The base field does not contain a cube root of unity.")
        x_im = x + y + z
        y_im = x + omega*y + omega**2*z
        z_im = x + omega**2*y + omega*z

        return self._parent([x_im, y_im, z_im], check=False)

    def _scale(self, s, t):
        """
            Given `self = (x : y : z)`, output `(s * x : t * y : t * z)`

            COST: 3 M
        """
        x, y, z = self.xyz()
        x_im = s * x # 1 M
        y_im = t * y # 1 M
        z_im = t * z # 1 M

        return self._parent([x_im, y_im, z_im], check=False)

    def evaluate_phi_1(self):
        """
            COST: 6M + 3S + 2 M_d
        """
        a,d = self._parent._a, self._parent._d

        P = self._cubing() # 3 S + 3 M
        P = P._DFT() # 0
        P = P._scale(1,d) # 2 M_d

        Hp = P._parent._special_isogeny_neighbour()
        return Hp([P._x, P._y, P._z])

    def triple(self):
        """
        Compute `3*self`.

        NOTE: Tripling as computed as a composition of 3-isogenies.

        COST: 12M + 6S + 4 M_d
        """
        Q = self.evaluate_phi_1()
        P = Q.evaluate_phi_1()

        return P


class HessianKummerLine(SageObject):
    r"""
    The Kummer line of an elliptic curve in Hessian form.

    EXAMPLES::

        sage: Fp = FiniteField(13)
        sage: H = EllipticCurveHessianForm(Fp(1),Fp(3))
        sage: HK = HessianKummerLine(H); HK
        Kummer Line of Elliptic Curve in Hessian form defined by 3*x^3 + y^3 - 3*x*y*z + z^3 over Finite Field of size 13
    """

    def __init__(self, curve):
        r"""
        Constructor for a Kummer line from an elliptic curve in Hessian form.
        """
        self._curve = curve
        self._base_ring = curve.base_ring()
        self._a = curve._a
        self._d = curve._d
        self._isogeny_neighbour = None

    def __repr__(self):
        r"""
        String representation of the Kummer line.
        """
        return f"Kummer Line of {self._curve}"

    def __call__(self, coords):
        r"""
        Create a Kummer point from the coordinates.
        """
        return HessianKummerLinePoint(self, coords)

    def _special_isogeny_neighbour(self):
        """
        Compute the Kummer line of a (special) 3-isogenous neighbour

        This concerns the 3-isogeny H -> H' with kernel <(0: 1 : omega)>.
        """
        if self._isogeny_neighbour:
            return self._isogeny_neighbour
        else:
            a1 = self._d**3 - self._a
            d1 = self._d

            E1 = EllipticCurveHessianForm(d1, a=a1)
            self._isogeny_neighbour = HessianKummerLine(E1)
            self._a1 = a1
            self._d1 = d1

            return self._isogeny_neighbour


class HessianKummerLinePoint(SageObject):
    r"""
    Class for representing points on the Kummer line of
    an elliptic curve in Hessian form.

    EXAMPLES:

    We create a HessianKummerLine from a given elliptic curve (with full 3-torsion)::

        sage: Fp = FiniteField(31)
        sage: E = EllipticCurve(Fp,[9,13])
        sage: H = EllipticCurveHessianForm(Fp(4)); H
        Elliptic Curve in Hessian form defined by x^3 + y^3 - 12*x*y*z + z^3 over Finite Field of size 31
        sage: H.j_invariant() == E.j_invariant()
        True
        sage: HK = HessianKummerLine(H); HK
        Kummer Line of Elliptic Curve in Hessian form defined by x^3 + y^3 - 12*x*y*z + z^3 over Finite Field of size 31

    We can create points on the Kummer line by directly passing Kummer coordinates
    (it is not tested if there exists a rational lift), or by passing points from
    the elliptic curve::

        sage: P = H([2,2,1]); P
        (2 : 2 : 1)
        sage: Q = HK(P); Q
        (2 : 3)
        sage: Q == HK([2,3])
        True

    We test the arithmetic. Currently, differential addition, doubling
    and tripling are implemented::

        sage: P1 = H([16,1,1])
        sage: P2 = H([24,7,1])
        sage: P2m = P2.negate()
        sage: P3 = P1.add(P2m); P3
        (7 : 15 : 28)
        sage: Q1 = HK(P1)
        sage: Q2 = HK(P2)
        sage: Q3 = HK(P3)
        sage: Q4 = Q1.xADD(Q2,Q3); Q4
        (8 : 27)
        sage: Q4 == HK(P1.add(P2))
        True
        sage: Q1.xDBL() == HK(P1.double())
        True
        sage: T = Q1.xTRPL(); T
        (25 : 7)
        sage: T == HK(P1.double().add(P1))
        True
    """

    def __init__(self, parent, coords):
        r"""
        Constructs the point P = (x : y + z) on the Kummer line `parent`
        on input a point (x : y : z) on the Hessian curve.

        Alternatively, the input can directly be a tuple (x, u) representing a curve on the Kummer line.
        """
        if isinstance(coords, EllipticCurveHessianPoint):
            coords = coords.xyz()
        K = parent._base_ring
        self._base_ring = K

        self._parent = parent

        if len(coords) == 3:
            self._x = K(coords[0])
            self._u = K(coords[1] + coords[2])

        if len(coords) == 2:
            self._x = K(coords[0])
            self._u = K(coords[1])


    def _repr_(self):
        """
        String representation.
        """
        s = "(%s " % self._x
        s += ": %s)" % self._u
        return s

    def xu(self):
        return self._x, self._u

    def __eq__(self,other):
        x1, u1 = self.xu()
        x2, u2 = other.xu()
        return x2*u1 == x1*u2

    def xADD(self, Q, PQ):
        r"""
        Compute the sum of two points P, Q on a the Hessian Kummer Line.
        PQ are the Kummer coordinates of P-Q

        COST: 15 M (+ 1 M_a + 5 M_d)
        """
        a = self._parent._a
        d = self._parent._d

        x1,u1 = self._x, self._u
        x2,u2 = Q._x, Q._u
        x3,u3 = PQ._x, PQ._u

        x1x2 = x1*x2
        x1u2 = x1*u2
        x2u1 = x2*u1
        u1u2 = u1*u2
        # 4 M
        ax1x2 = a*x1x2
        # 1 M_a
        dx1x2 = d*x1x2
        dx1u2 = d*x1u2
        dx2u1 = d*x2u1
        du1u2 = d*u1u2
        term = (3*d**2-2)*x1x2
        # 5 M_d
        u34 =  - (ax1x2+ax1x2) * (dx1x2 + x1u2 + x2u1) - u1u2*(term + x1x2  + x1x2 + (dx1u2 + dx2u1) + u1u2)
        # 2 M
        x3p  =  - x1x2 * (ax1x2-du1u2) + x2u1 * (dx2u1+u1u2) + x1u2 * (dx1u2+u1u2)
        # 3 M
        u4 = u34*x3 - u3*x3p
        x4 = x3 * x3p
        # 3 M

        return self._parent((x4,u4))

    def xDBL(self):
        """
        Double the point.

        COST: 4M + 3S + 1M_a + 1M_d
        """
        a,d = self._parent._a, self._parent._d
        x1,u1 = self._x, self._u
        x12 = x1*x1 # S
        x13 = x1*x12 # M
        ax13 = a*x13 # a
        dx1 = d*x1  # d
        u12 = u1*u1 # S
        u14 = u12*u12 # S

        u2 = -  ax13*(3*dx1 + 4*u1) - u14 # 1 M
        x2 = x1 * (-ax13 + (3*dx1 + u1 + u1)*u12) # 2M

        return self._parent((x2,u2))

    def _cubing(self):
        """
        On input (x, u=y+z), compute (x^3, y^3 + z^3).

        COST: 2 S + 2 M + 1 M_a + 2 M_d
        """
        a,d = self._parent._a, self._parent._d
        x,u = self._x, self._u

        x2 = x * x # 1 S
        u2 = u * u # 1 S

        ax2 = a * x2 # 1 M_a
        dx = d * x # 1 M_d
        du2 = d * u2 # 1 M_d

        x_im = ax2 * (u + dx) # 1 M
        u_im = u * (du2 - ax2) # 1 M

        #Note: technically, the point is no longer on the same Kummer line
        return self._parent((x_im, u_im))

    def _DFT(self):
        """
        Given x, u, output x + u, 2*x - u

        COST: 0
        """
        u, x = self._u, self._x
        x_im = x + u
        u_im = x + x - u

        #Note: technically, the point is no longer on the same Kummer line
        return self._parent((x_im, u_im))

    def _scale(self, s, t):
        """
            Given `self = (x : u)`, output `(s * x : t * u)`

            COST: 2 M
        """
        u, x = self._u, self._x
        x_im = s * x # 1 M
        u_im = t * u # 1 M

        #Note: technically, the point is no longer on the same Kummer line
        return self._parent((x_im, u_im))

    def evaluate_phi_1(self):
        """
            COST: 2M + 2S + 1 M_a + 3 M_d
        """
        a,d = self._parent._a, self._parent._d

        P = self._cubing() # 2 S + 2 M + 1 M_a + 2 M_d
        P = P._DFT() # 0
        P = P._scale(1,d) # 1 M_d #double check, if need multiplication by 3 here!

        new_HK = P._parent._special_isogeny_neighbour()
        return new_HK([P._x, P._u])


    def xTRPL(self):
        """
        Triple the point.

        NOTE: Tripling as computed as a composition of 3-isogenies.

        COST: 4M + 4S + 2 M_a + 6 M_d
        """
        Q = self.evaluate_phi_1()
        P = Q.evaluate_phi_1()

        return P