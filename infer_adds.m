////////////////////////////////////////////////////////////////////////
// 0. Base field Q(omega)
////////////////////////////////////////////////////////////////////////

Q<x> := PolynomialRing(Rationals());
K0<omega> := ext< Rationals() | x^2 + x + 1 >;

////////////////////////////////////////////////////////////////////////
// 1. Polynomial ring
//    h0..h4, t0..t4, x0..x8, symmetric M_ij
////////////////////////////////////////////////////////////////////////

R := PolynomialRing(K0, 
    5   // h
  + 5   // t
  + 9   // x
  + 15  // symmetric M
);

AssignNames(~R,
[
"h0","h1","h2","h3","h4",
"t0","t1","t2","t3","t4",
"x0","x1","x2","x3","x4","x5","x6","x7","x8",
"M00","M01","M02","M03","M04",
      "M11","M12","M13","M14",
            "M22","M23","M24",
                  "M33","M34",
                        "M44"
]);

////////////////////////////////////////////////////////////////////////
// 2. Symmetric 5x5 matrix M
////////////////////////////////////////////////////////////////////////

M := Matrix(R,5,5,
[
M00,M01,M02,M03,M04,
M01,M11,M12,M13,M14,
M02,M12,M22,M23,M24,
M03,M13,M23,M33,M34,
M04,M14,M24,M34,M44
]);

////////////////////////////////////////////////////////////////////////
// 3. Quadratic equations of the surface
////////////////////////////////////////////////////////////////////////

quadratics := [
    h0*x0^2 + h1*x1*x2 + h2*x3*x6 + h4*x5*x7 + h3*x4*x8,
    h0*x1^2 + h1*x0*x2 + h3*x5*x6 + h2*x4*x7 + h4*x3*x8,
    h1*x0*x1 + h0*x2^2 + h4*x4*x6 + h3*x3*x7 + h2*x5*x8,
    h0*x3^2 + h1*x4*x5 + h2*x0*x6 + h3*x2*x7 + h4*x1*x8,
    h0*x4^2 + h1*x3*x5 + h4*x2*x6 + h2*x1*x7 + h3*x0*x8,
    h1*x3*x4 + h0*x5^2 + h3*x1*x6 + h4*x0*x7 + h2*x2*x8,
    h2*x0*x3 + h4*x2*x4 + h3*x1*x5 + h0*x6^2 + h1*x7*x8,
    h3*x2*x3 + h2*x1*x4 + h4*x0*x5 + h0*x7^2 + h1*x6*x8,
    h4*x1*x3 + h3*x0*x4 + h2*x2*x5 + h1*x6*x7 + h0*x8^2
];

////////////////////////////////////////////////////////////////////////
// 4. Null point and its parameter relations
////////////////////////////////////////////////////////////////////////

OO := [ t0, t1, t1, t2, t3, t4, t2, t4, t3 ];

null_relations := [
    t0^2*h0 + t1^2*h1 + t2^2*h2 + t3^2*h3 + t4^2*h4,
    t1^2*h0 + t0*t1*h1 + t3*t4*h2 + t2*t4*h3 + t2*t3*h4,
    t2^2*h0 + t3*t4*h1 + t0*t2*h2 + t1*t4*h3 + t1*t3*h4,
    t3^2*h0 + t2*t4*h1 + t1*t4*h2 + t0*t3*h3 + t1*t2*h4,
    t4^2*h0 + t2*t3*h1 + t1*t3*h2 + t1*t2*h3 + t0*t4*h4
];

////////////////////////////////////////////////////////////////////////
// 5. Vector form P^8 -> (P^4)^9
////////////////////////////////////////////////////////////////////////

function VectorForm(A)
    A0,A1,A2,A3,A4,A5,A6,A7,A8 := Explode(A);

    return [
        Vector([A0^2, A1*A2, A3*A6, A4*A8, A5*A7]),
        Vector([A1^2, A0*A2, A4*A7, A5*A6, A3*A8]),
        Vector([A2^2, A0*A1, A5*A8, A3*A7, A4*A6]),
        Vector([A3^2, A4*A5, A0*A6, A2*A7, A1*A8]),
        Vector([A4^2, A3*A5, A1*A7, A0*A8, A2*A6]),
        Vector([A5^2, A3*A4, A2*A8, A1*A6, A0*A7]),
        Vector([A6^2, A7*A8, A0*A3, A1*A5, A2*A4]),
        Vector([A7^2, A6*A8, A4*A1, A2*A3, A0*A5]),
        Vector([A8^2, A6*A7, A5*A2, A0*A4, A1*A3])
    ];
end function;

////////////////////////////////////////////////////////////////////////
// 6. Projective equations for addition
////////////////////////////////////////////////////////////////////////

function ToEquations(P, Q, Rres)
    VP := VectorForm(P);
    VQ := VectorForm(Q);

    XX := [ (VP[i] * M * Transpose(VQ[i]))[1] : i in [1..9] ];

    eqs := [];
    for i in [1..8] do
        Append(~eqs, XX[i]*Rres[i+1] - XX[i+1]*Rres[i]);
    end for;
    Append(~eqs, XX[9]*Rres[1] - XX[1]*Rres[9]);

    return eqs;
end function;

////////////////////////////////////////////////////////////////////////
// 7. Automorphisms and negation
////////////////////////////////////////////////////////////////////////

function sig1(P)
    return [ P[2],P[3],P[1], P[5],P[6],P[4], P[8],P[9],P[7] ];
end function;

function sig2(P)
    return [ P[4],P[5],P[6], P[7],P[8],P[9], P[1],P[2],P[3] ];
end function;

function tau1(P)
    return [
        P[1],
        omega*P[2], omega^2*P[3],
        P[4],
        omega*P[5], omega^2*P[6],
        P[7],
        omega*P[8], omega^2*P[9]
    ];
end function;

function tau2(P)
    return [
        P[1],P[2],P[3],
        omega*P[4],omega*P[5],omega*P[6],
        omega^2*P[7],omega^2*P[8],omega^2*P[9]
    ];
end function;

function neg(P)
    return [ P[1],P[3],P[2], P[7],P[9],P[8], P[4],P[6],P[5] ];
end function;

////////////////////////////////////////////////////////////////////////
// 8. Three-torsion relations: P+P = -P
////////////////////////////////////////////////////////////////////////

three_torsion := [
    sig1(OO),
    sig2(OO),
    tau1(OO),
    tau2(OO)
];

add_eqs := [];
for P in three_torsion do
    add_eqs cat:= ToEquations(P, P, neg(P));
end for;

////////////////////////////////////////////////////////////////////////
// 9. Final ideal and Gröbner basis
////////////////////////////////////////////////////////////////////////

I := ideal< R |
    quadratics,
    null_relations,
    add_eqs
>;

////////////////////////////////////////////////////////////////////////
// 10. Elimination: remove x_i, t_i
////////////////////////////////////////////////////////////////////////

ElimVars := [
x0,x1,x2,x3,x4,x5,x6,x7,x8,
t0,t1,t2,t3,t4
];

J := EliminationIdeal(I, ElimVars);

GB := GroebnerBasis(J);
GB;
