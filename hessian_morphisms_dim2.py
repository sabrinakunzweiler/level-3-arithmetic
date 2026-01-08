import sys
sys.path.append(".")

from sage.misc.cachefunc import cached_method
#from sage.structure.richcmp import richcmp_not_equal, richcmp, op_EQ, op_NE

from sage.categories.morphism import Morphism
from sage.rings.integer_ring import ZZ
from sage.rings.finite_rings import finite_field_base
from sage.rings.number_field import number_field_base
from sage.structure.element import RingElement
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from hessian_arithmetic_dim2 import AbelianSurfaceHessianForm
from hessian_arithmetic_dim2 import AbelianSurfaceHessianPoint


class AbelianSurfaceHessianFormHom(Morphism):
    """
    Base class for morphisms of abelian surfaces in Hessian form.
    """

    def _burkhardt_check(self, scalars):
        """
        Check that the transformation defined by the scalars is
        an automorphism of the Burkhardt quartic.
        """
        K = self._base_ring
        R = PolynomialRing(K,"x",5)
        x0,x1,x2,x3,x4 = R.gens()
        c0,c1,c2,c3,c4 = scalars
        F = x0*(x0**3 + x1**3 + x2**3 + x3**3 + x4**3) + 3*x1*x2*x3*x4
        G = F(c0*x0,c1*x1,c2*x2,c3*x3,c4*x4)
        return F == G*c0**4

    def _DFT_Burkhardt(self, P):
        """
        Apply the discrete Fourier transform to a point on the
        Burkhardt quartic.
        """
        u0,u1,u2,u3,u4 = P
        y0 = u0 + u1 + u2 + u3 + u4
        y1 = 2*u0 - u1 + 2*u2 - u3 - u4
        y2 = 2*u0 + 2*u1 - u2 - u3 - u4
        y3 = 2*u0 - u1 - u2 - u3 + 2*u4
        y4 = 2*u0 - u1 - u2 + 2*u3 - u4
        return (y0,y1,y2,y3,y4)

    def _DFT_Burkhardt_transpose(self, P):
        """
        Apply the transpose of the Fourier transform to a point.
        """
        u0,u1,u2,u3,u4 = P
        y0 = u0 + 2*u1 + 2*u2 + 2*u3 + 2*u4
        y1 = u0 - u1 + 2*u2 - u3 - u4
        y2 = u0 + 2*u1 - u2 - u3 - u4
        y3 = u0 - u1 - u2 - u3 + 2*u4
        y4 = u0 - u1 - u2 + 2*u3 - u4
        return (y0,y1,y2,y3,y4)

    def _scale(self, P, scalars):
        """
        Pointwise scaling of the point `P` by `scalars`
        """
        u0,u1,u2,u3,u4 = P
        c0,c1,c2,c3,c4 = scalars
        return c0*u0, c1*u1, c2*u2, c3*u3, c4*u4

    def _scale_inverse(self, P, scalars):
        """
        Pointwise scaling of the point `P` by the inverse of `scalars`
        """
        u0,u1,u2,u3,u4 = P
        c0,c1,c2,c3,c4 = scalars
        #return u0/c0, u1/c1, u2/c2, u3/c3, u4/c4
        return u0*c1*c2*c3*c4, c0*u1*c2*c3*c4, c0*c1*u2*c3*c4, c0*c1*c2*u3*c4, c0*c1*c2*c3*u4

    def _find_scalars(self, P1, P2):
        """
        Auxiliary function to compute the correct scalars for a 3-isogeny.

        Input:
            - coordinates of 9-torsion points: P1, P2
               with 3 * P1 = +/- [s1,s0,s1, ...],
               3 * P2 = +/-[s2,*,*,s0,*,*,s2,*,*]
               TODO: make this precise!
            Output:
            - scalars c0,c1,c2,c3,c4 for the 3-isogeny with kernel 3*(P1,P2)

            COST: 27S + 37M
        """
        OO = self._domain._neutral_element

        OO = OO._cubing() # 9S + 9M
        P1 = P1._cubing() # 9S + 9M
        P2 = P2._cubing() # 9S + 9M

        OO = OO._DFT()
        P1 = P1._DFT()
        P2 = P2._DFT()

        # scalars
        #l0 = 1
        #l1 = P1[0]/P1[1]
        #l2 = P2[0]/P2[3]
        #l3 = P1[6]/P1[4]*l2
        #l4 = P1[8]/P1[5]*l3

        l0 = P1[1]*P1[4]*P1[5]*P2[3] # 3M
        l1 = P1[0]*P1[4]*P1[5]*P2[3] # 1M
        l2 = P1[1]*P1[4]*P1[5]*P2[0] # 2M
        l3 = P1[1]*P1[5]*P1[6]*P2[0] # 3M
        l4 = P1[1]*P1[6]*P1[8]*P2[0] # 1M

        return l0,l1,l2,l3,l4

    def _find_dual_scalars(self, c0, c1, c2, c3, c4):
        """
            Find the scalars defining the dual isogeny

            Input:
            - `c0, ... , c4` : scalars defining a (3,3)-isogeny

            Output:
            - `e0, ... , e4` : scalars defining the dual isogeny

            COST: 34 M + 18 S
        """

        OO = self._domain._neutral_element

        s0 = OO[0]
        s1 = OO[1]
        s2 = OO[3]
        s3 = OO[4]
        s4 = OO[5]

        #image of OO under (non-scaled isogeny)
        P =  OO
        P = P._cubing() # 9M + 9S
        P = P._DFT()
        P = P._scale([c0,c1,c2,c3,c4]) # 9M
        P = P._cubing() # 9M + 9S
        P = P._DFT()

        # compare OO with 3*OO
        s0 = OO[0]
        s1 = OO[1]
        s2 = OO[3]
        s3 = OO[4]
        s4 = OO[5]
        #
        t0 = P[0]
        t1 = P[1]
        t2 = P[3]
        t3 = P[4]
        t4 = P[5]

        # sanity check
        assert P[2] == t1 and P[6] == t2 and P[7] == t4 and P[8] == t3

        t01 = t0*t1 # 1 M
        t34 = t3*t4 # 1 M
        e0 = s0*t1*t2*t34 # 3M
        e1 = s1*t0*t2*t34 # 3M
        e2 = s2*t01*t34 # 2M
        e3 = s3*t01*t2*t4 # 3M
        e4 = s4*t01*t2*t3 # 3M

        return e0,e1,e2,e3,e4


    def __init__(self, domain, args, kwd, check=True, scalars=None, auxP=None):
        r"""
        Constructor for morphisms of abelian surfaces in Hessian form.

        INPUT:

            - domain: The domain of the morphism (a p.p.a.s. in Hessian form)
            - args: a scaling vector if the morphism is a scaling,
                or a tuple consisting of two 9-torsion points
            - kwd: a keyword determining the type of morphism. Allowed keywords are:
                    "scaling", "DFT", "isogeny"
            - auxP: auxiliary point on the domain. Required if the codomain of an isogeny is reducible.

        EXAMPLES::


        """

        self._domain = domain
        self._base_ring = domain._base_ring
        self._kwd = kwd
        OO = domain._neutral_element
        d = domain._d
        h = domain._h
        self._codomain = None

        if kwd == "dual":
            phi = args
            scalars = phi._scalars
            assert domain == phi._codomain
            dual_scalars = phi._find_dual_scalars(*scalars)
            self._scalars = dual_scalars
            self._codomain = phi._domain

        elif kwd == "scaling":
            scalars = args
            assert len(scalars) == 5
            self._scalars = scalars
            if check:
                assert self._burkhardt_check(scalars)
            new_d = self._scale_inverse(d, scalars)
            new_h = self._scale(h, scalars)
            new_OO = OO._scale(scalars)

        elif kwd == "DFT":
            new_d = self._DFT_Burkhardt_transpose(d)
            new_h = self._DFT_Burkhardt(h)
            new_OO = OO._DFT()

        elif kwd == "isogeny":
            R1,R2 = args #two 9-torsion points above the kernel, one extra point
            self._scalars = self._find_scalars(R1,R2)

            new_OO = OO._cubing()
            new_OO = new_OO._DFT()
            new_OO = new_OO._scale(self._scalars) #note that this is also computed earlier
            if auxP:
                auxP = auxP._cubing()
                auxP = auxP._DFT()
                auxP = auxP._scale(self._scalars)
                new_d = auxP._compute_d()
                new_h = auxP._compute_h()
            else:
                new_d = new_OO._compute_d()
                new_h = new_OO._compute_h()

        elif kwd == "negation": #this is an automorphism
            new_OO = OO
            new_h = h
            new_d = d

        if not self._codomain:
            self._codomain = AbelianSurfaceHessianForm([new_d, new_h], omega=self._domain._omega)
            self._codomain._neutral_element = self._codomain(new_OO._coords)
        # TODO:check if the following works
        self._domain._phi = self

    def is_isomorphism(self):
        """
        Return True if `self` is an isomorphism.
        """
        return self._kwd == "scaling" or self._kwd == "DFT" or self._kwd == "negation"

    def dual(self):
        """
        Compute the dual isogeny of self.
        """
        assert self._kwd == "isogeny"
        return AbelianSurfaceHessianFormHom(self.codomain(), self, "dual")

    def codomain(self):
        """
        Return the codomain of `self`
        """
        return self._codomain

    def domain(self):
        """
        Return the domain of `self`
        """
        return self._domain

    def _repr_(self):
        """
        String representation.
        """

        if self._kwd == "scaling":
            s = "Scaling morphisms with scalars "
            s += str(self._scalars)
        elif self._kwd == "DFT":
            s = "Discrete Fourier transform "
        elif self._kwd == "isogeny" or self._kwd == "dual":
            s = "(3,3)-isogeny "
        if self._kwd == "negation":
            s = "multiplication by [-1]"

        s += "\n domain: " + str(self.domain())
        s += "\n codomain: " + str(self.codomain())

        return s

    def __call__(self, P):
        """
        Return the image of the point P under the morphism.
        """
        #assert isinstance(P, AbelianSurfaceHessianPoint)
        #coords = P._coords
        if self._kwd == "scaling":
            P = P._scale(self._scalars)
        elif self._kwd == "DFT":
            P = P._DFT()
        elif self._kwd == "isogeny" or self._kwd == "dual":
            P = P._cubing()
            P = P._DFT()
            P = P._scale(self._scalars)
        if self._kwd == "negation" or self._kwd == "dual":
            return self._codomain(P._coords).negate()
        else:
            return self._codomain(P._coords)




class AbelianSurfaceHessianFormCompositeHom(Morphism):
    """
    Base class to represent composite morphisms of
    abelian surfaces in Hessian form.
    """
    def __init__(self, morphism_list, check=True):
        r"""
        Constructor for composite morphisms of abelian surfaces in Hessian form.

        INPUT:

            - morphism_list a list of morphisms phi1, ..., phin
            defining the morphism phin \circ ... \circ phi1

        EXAMPLES::


        """
        n = len(morphism_list)
        if check:
            for i in range(n-1):
                assert(morphism_list[i].codomain() == morphism_list[i+1].domain())

        self._domain = morphism_list[0].domain()
        self._codomain = morphism_list[-1].codomain()
        self._base_ring = self._domain._base_ring
        self._maps = morphism_list

    def _repr_(self):
        """
        String representation.
        """
        s = "Composite morphism of abelian surfaces in Hesse form"
        s += "\ndomain: " + str(self._domain)
        s += "\ncodomain: " + str(self._codomain)
        return s

    def __call__(self, P):
        """
        Return the image of the point P under the morphism.
        """

        for phi in self._maps:
            P = phi(P)

        return P

    def domain(self):
        """
        Return the domain of `self`
        """
        return self._domain

    def codomain(self):
        """
        Return the codomain of `self`
        """
        return self._codomain
