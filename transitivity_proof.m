F<z> := CyclotomicField(3);
M := Matrix(F,5,5,
    [1, 2, 2, 2, 2,
     1, -1, 2, -1, -1,
     1, 2, -1, -1, -1,
     1, -1, -1, -1, 2,
     1, -1, -1, 2, -1]);

function a0(h)
 h0,h1,h2,h3,h4 := Explode(h); return [z*h0,h1,z*h2,h3,h4];
end function;

function a0sq(h)
 h0,h1,h2,h3,h4 := Explode(h); return [z^2*h0,h1,z^2*h2,h3,h4];
end function;

function a1(h)
 h0,h1,h2,h3,h4 := Explode(h); return [h0,h1,h2,z*h3,z^2*h4];
end function;

function a1sq(h)
 h0,h1,h2,h3,h4 := Explode(h); return [h0,h1,h2,z^2*h3,z*h4];
end function;

function a2(h);
 h0,h1,h2,h3,h4 := Explode(h); return [z*h0,z*h1,h2,h3,h4];
end function;

function a2sq(h);
 h0,h1,h2,h3,h4 := Explode(h); return [z^2*h0,z^2*h1,h2,h3,h4];
end function;

function DFT(h)
 hmat := Matrix(F,1,5,h);
 h := hmat*M;
 return [h[1,i] : i in [1..5]];
end function;

function transform(h)

 if h eq [0,0,0,-1,1] then h := h;
 elif h eq [0,0,0,-z,1] then h := a1(h);
 elif h eq [0,0,0,-z^2,1] then h := a1sq(h);
 elif h eq [1,-1,-1,-z^2,-z] then h := a1(DFT(h));
 elif h eq [1,-1,-1,-z,-z^2] then h := a1sq(DFT(h));
 elif h eq [1,-z,-1,-1,-z^2] then h := a1(DFT(a0(h)));
 elif h eq [1,-z^2,-1,-z,-1] then h := a1(DFT(a0sq(h)));
 elif h eq [1,-1,-z,-1,-z^2] then h := a1(DFT(a2(h)));
 elif h eq [1,-1,-z^2,-z,-1] then h := a1(DFT(a2sq(h)));
 elif h eq [1,-z,-1,-z^2,-1] then h := a1sq(DFT(a0(h)));
 elif h eq [1,-z^2,-1,-1,-z] then h := a1sq(DFT(a0sq(h)));
 elif h eq [1,-1,-1,-1,-1] then h := a1sq(DFT(a1(h)));
 elif h eq [1,-1,-z,-z^2,-1] then h := a1sq(DFT(a2(h)));
 elif h eq [1,-1,-z^2,-1,-z] then h := a1sq(DFT(a2sq(h)));
 
 elif h eq [1,-z,-z,-z,-1] then h := a1(DFT(a0(a2(h))));
 elif h eq [0,0,-z,1,0] then h := a1(DFT(a0(DFT(h))));
 elif h eq [1,-z^2,-z,-z^2,-z] then h := a1(DFT(a0sq(a2(h))));
 elif h eq [0,0,-z^2,0,1] then h := a1(DFT(a0sq(DFT(h))));
 elif h eq [0,-z,0,1,0] then h := a1(DFT(a2(DFT(h))));
 elif h eq [1,-z,-z^2,-z^2,-z] then h := a1(DFT(a2sq(a0(h))));
 elif h eq [0,-z^2,0,0,1] then h := a1(DFT(a2sq(DFT(h))));
 elif h eq [1,-z,-1,-z,-z] then h := a1sq(DFT(a0(a1(h))));
 elif h eq [1,-z,-z,-1,-z] then h := a1sq(DFT(a0(a2(h))));
 elif h eq [0,0,-z,0,1] then h := a1sq(DFT(a0(DFT(h))));
 elif h eq [1,-z^2,-1,-z^2,-z^2] then h := a1sq(DFT(a0sq(a1(h))));
 elif h eq [1,-z^2,-z,-z,-z^2] then h := a1sq(DFT(a0sq(a2(h))));
 elif h eq [1,-z^2,-z^2,-z^2,-1] then h := a1sq(DFT(a0sq(a2sq(h))));
 elif h eq [0,0,-z^2,1,0] then h := a1sq(DFT(a0sq(DFT(h))));
 elif h eq [1,-1,-z,-z,-z] then h := a1sq(DFT(a2(a1(h))));
 elif h eq [0,-z,0,0,1] then h := a1sq(DFT(a2(DFT(h))));
 elif h eq [1,-z,-z^2,-z,-z^2] then h := a1sq(DFT(a2sq(a0(h))));
 elif h eq [1,-1,-z^2,-z^2,-z^2] then h := a1sq(DFT(a2sq(a1(h))));
 elif h eq [0,-z^2,0,1,0] then h := a1sq(DFT(a2sq(DFT(h))));

 elif h eq [0,0,-1,0,1] then h := a1(DFT(a0sq(DFT(a0sq(h)))));
 elif h eq [0,-1,0,0,1] then h := a1(DFT(a2sq(DFT(a2sq(h)))));
 elif h eq [0,0,-1,1,0] then h := a1(DFT(a0(DFT(a0(h)))));
 elif h eq [0,-1,0,1,0] then h := a1(DFT(a2(DFT(a2(h)))));
 elif h eq [1,-z,-z,-z^2,-z^2] then h := a1sq(DFT(a0(a2(a1(h)))));
 elif h eq [1,-z,-z^2,-1,-1] then h := a1(DFT(a2sq(a0(a1sq(h)))));
 elif h eq [1,-z^2,-z,-1,-1] then h := a1sq(DFT(a0sq(a2(a1(h)))));
 elif h eq [1,-z^2,-z^2,-z,-z] then h := a1sq(DFT(a2sq(a1(a0sq(h)))));
 elif h eq [1,-z^2,-z^2,-1,-z^2] then h := a1sq(DFT(a0sq(a2sq(a1sq(h)))));

 elif h eq [0,-z,1,0,0] then h := a1sq(DFT(a0sq(a2(a1(DFT(h))))));
 elif h eq [0,-z^2,1,0,0] then h := a1(DFT(a2sq(a0(a1sq(DFT(h))))));
 elif h eq [0,-1,1,0,0] then h := a1sq(DFT(a0sq(a2(a1(DFT(a2(h)))))));
 end if;
 k := h[5]; if k eq 0 then k := h[4]; end if; if k eq 0 then k := h[3]; end if;
 h := [h[j]/k : j in [1..5]]; // Normalize
 return h;
end function;

I := [0,1,2];
for i in I do for j in I do for k in I do
 h := [1,-z^i,-z^j,-z^k,-z^(-i-j-k)];
 assert transform(h) eq [0,0,0,-1,1];
end for; end for; end for;

for i in [2..4] do for j in I do
 h := [F! 0,0,0,0,1]; h[i] := -z^j;
 assert transform(h) eq [0,0,0,-1,1];
end for; end for;

for i in [2..3] do for j in I do
 h := [F! 0,0,0,1,0]; h[i] := -z^j;
 assert transform(h) eq [0,0,0,-1,1];
end for; end for;

for i in [2..2] do for j in I do
 h := [F! 0,0,1,0,0]; h[i] := -z^j;
 assert transform(h) eq [0,0,0,-1,1];
end for; end for;
