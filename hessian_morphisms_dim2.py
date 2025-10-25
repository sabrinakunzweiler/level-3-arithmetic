from sage.misc.cachefunc import cached_method
#from sage.structure.richcmp import richcmp_not_equal, richcmp, op_EQ, op_NE

from sage.categories.morphism import Morphism
from sage.rings.integer_ring import ZZ
from sage.rings.finite_rings import finite_field_base
from sage.rings.number_field import number_field_base


from hessian_arithmetic_dim2 import AbelianSurfaceHessianForm

class AbelianSurfaceHessianFormHom(Morphism):
    """
    Base class for morphisms of abelian surface in Hessian form.
    """

    def _burkhardt_check(self, scalars):
        """
        Check that the transformation defined by the scalars is
        an automorphism of the Burkhardt quartic.
        """
        K = self._base_ring
        R = PolynomialRing(5, K)
        x0,x1,x2,x3,x4 = R.gens()
        c0,c1,c2,c3,c4 = scalars
        F = x0*(x0**3 + x1**3 + x2**3 + x3**3 + x4**3) + 3*x1*x2*x3*x4
        G = F(c0*x0,c1*x1,c2*x2,c3*x3,c4*x4)/c0**4
        return F == G

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
        return u0/c0, u1/c1, u2/c2, u3/c3, u4/c4

    def _scale_long(self, P, scalars):
        """
        Pointwise scaling of a point on the abelian variety,
        resepcting multiplication by -1.
        """
        x0,x1,x2,x3,x4,x5,x6,x7,x8 = P
        c0,c1,c2,c3,c4 = scalars

        y0 = c0*x0
        y1 = c1*x1
        y2 = c1*x2
        y3 = c2*x3
        y4 = c3*x4
        y5 = c4*x5
        y6 = c2*x6
        y7 = c4*x7
        y8 = c3*x8

        return y0,y1,y2,y3,y4,y5,y6,y7,y8

    def _DFT(self, P):
        """
            Apply the discrete Fourier transform.

            COST: 0
        """
        omega = self._domain._omega
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = P
        y0 = x0 + x1          + x2          + x3          + x4          + x5          + x6          + x7          + x8
        y1 = x0 + omega*x1    + omega**2*x2 + x3          + omega*x4    + omega**2*x5 + x6          + omega*x7    + omega**2*x8
        y2 = x0 + omega**2*x1 + omega*x2    + x3          + omega**2*x4 + omega*x5    + x6          + omega**2*x7 + omega*x8
        y3 = x0 + x1          + x2          + omega*x3    + omega*x4    + omega*x5    + omega**2*x6 + omega**2*x7 + omega**2*x8
        y4 = x0 + omega*x1    + omega**2*x2 + omega*x3    + omega**2*x4 + x5          + omega**2*x6 + x7          + omega*x8
        y5 = x0 + omega**2*x1 + omega*x2    + omega*x3    + x4          + omega**2*x5 + omega**2*x6 + omega*x7    + x8
        y6 = x0 + x1          + x2          + omega**2*x3 + omega**2*x4 + omega**2*x5 + omega*x6    + omega*x7    + omega*x8
        y7 = x0 + omega*x1    + omega**2*x2 + omega**2*x3 + x4          + omega*x5    + omega*x6    + omega**2*x7 + x8
        y8 = x0 + omega**2*x1 + omega*x2    + omega**2*x3 + omega*x4    + x5          + omega*x6    + x7          + omega**2*x8

        return y0,y1,y2,y3,y4,y5,y6,y7,y8

    def _cubing(self, P):
        """
        Coordinate-wise cubing of P in PP^8
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = P

        return x0**3,x1**3,x2**3,x3**3,x4**3,x5**3,x6**3,x7**3,x8**3

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

        OO = self._cubing(*OO) # 9S + 9M
        P1 = self._cubing(*P1) # 9S + 9M
        P2 = self._cubing(*P2) # 9S + 9M

        OO = self._DFT(*OO)
        P1 = self._DFT(*P1)
        P2 = self._DFT(*P2)


        #check what the correct indices are, below we use [2,6]
        # other possibility [1,3], or combinations

        l0 = P1[2]*P2[6] # 1M
        l1 = P1[0]*P2[6] # 1M
        l2 = P2[0]*P1[2] # 1M

        k0 = P1[8]*P1[7] # 1M
        l0 = l0*k0 # 1M
        l1 = l1*k0 # 1M
        l3 = l2*P1[3]*P1[7] # 2M
        l4 = l2*P1[3]*P1[4] # 1M
        l2 = l2*k0 # 1M

        return l0,l1,l2,l3,l4

    def _compute_d(self, P):
        """
        Compute the domain coefficients d0, ..., d4 given a point on the surface.

        INPUT:
            - arbitrary point P (not 3-torsion)

        OUTPUT:
            d0, ..., d4 defining the cubic equations.
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = P

        d0 = x0**3 + x1**3 + x2**3 + x3**3 + x4**3 + x5**3 + x6**3 + x7**3 + x8**3
        d1 = x0*x1*x2 + x3*x4*x5 + x6*x7*x8
        d2 = x0*x3*x6 + x1*x4*x7 + x2*x5*x8
        d3 = x0*x4*x8 + x1*x5*x6 + x2*x3*x7
        d4 = x0*x5*x7 + x1*x3*x8 + x2*x4*x6

        assert d0 != 0 #is this the only assertion?

        return d0,d1,d2,d3,d4

    def _compute_h(self, P):
        """
        Compute the domain coefficients h0, ..., h4 given a point on the surface.

        INPUT:
            - arbitrary point P (not 3-torsion)

        OUTPUT:
            h0, ..., h4 defining the quadratic equations.
        """
        x0, x1, x2, x3, x4, x5, x6, x7, x8 = P

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


    def __init__(self, domain, args, kwd, check=True):
        r"""
        Constructor for morphisms of abelian surfaces in Hessian form.

        EXAMPLES::


        """

        self._domain = domain
        self._base_ring = domain._base_ring
        self._kwd = kwd
        d = domain._d
        h = domain._h

        if kwd == "scaling":
            scalars = args
            assert len(scalars) == 5
            self._scalars = scalars
            if check:
                assert self._burkhardt_check(scalars)
            new_d = self._scale_inverse(d, scalars)
            new_h = self._scale(h, scalars)

        elif kwd == "DFT":
            new_d = self._DFT_Burkhardt_transpose(d)
            new_h = self._DFT_Burkhardt_transpose(h)

        elif kwd == "isogeny":
            R1,R2,P = args #two 9-torsion points above the kernel, one extra point (not 3-torsion on the codomain)
            self._scalars = self._find_scalars(R1,R2)
            # compute the image of P under the isogeny to compute the new parameters
            P = self._cubing(P)
            P = self._scale_long(P, self._scalars)
            P = self._DFT(P)
            new_d = self._compute_d(P)
            new_h = self._compute_h(P)


        self._codomain = AbelianSurfaceHessianForm(new_d, new_h)

    def is_isomorphism(self):
        """
        Return True if `self` is an isomorphism.
        """
        return kwd == "scaling" or kwd == "DFT"

    def __call__(self, P):
        """
        Return the image of the point P under the morphism.
        """
        assert isinstance(P, AbelianSurfaceHessianForm)
        coords = self._coords
        if self._kwd == "scaling":
            new_coords = self._scale_long(coords, self._scalars)

        elif kwd == "DFT":
            new_coords = self._DFT(coords)

        elif kwd == "isogeny":
            coords = self._cubing(coords)
            coords = self._scale_long(coords, self._scalars)
            new_coords = self._DFT(coords)

        return self._codomain(new_coords)







