(* ::Package:: *)

BeginPackage["riemann`"];


Differential::usage = ToString["Differential[{\!\(\*SubscriptBox[
StyleBox[\"x\",\nFontSlant->\"Italic\"], \(1\)]\), \!\(\*SubscriptBox[
StyleBox[\"x\",\nFontSlant->\"Italic\"], \(2\)]\), ...}] returns the list of symbols {\!\(\*SubscriptBox[
StyleBox[\(d\)
StyleBox[\"x\",\nFontSlant->\"Italic\"]], \(1\)]\), \!\(\*SubscriptBox[
StyleBox[\(d\)
StyleBox[\"x\",\nFontSlant->\"Italic\"]], \(2\)]\), ...}",StandardForm]
Metric::usage = ToString["Metric[\!\(\*
StyleBox[\"ds2\",\nFontSlant->\"Italic\"]\), {\!\(\*SubscriptBox[
StyleBox[\"x\",\nFontSlant->\"Italic\"], \(1\)]\), \!\(\*SubscriptBox[
StyleBox[\"x\",\nFontSlant->\"Italic\"], \(2\)]\), ...}] returns the metric tensor specified by the line element \!\(\*
StyleBox[\"ds2\",\nFontSlant->\"Italic\"]\) with coordinates \!\(\*SubscriptBox[
StyleBox[\"x\",\nFontSlant->\"Italic\"], \(i\)]\).",StandardForm]
Christoffel::usage = ToString["Christoffel[g,chart] returns the list of all Christoffel symbols for metric g in coordinates 'chart'",StandardForm]
CovD::usage = ToString[
"CovD[\[Omega],chart,\[CapitalGamma]] returns the covariant derivative of fully covariant tensor \[Omega] with Chrisoffel symbols \[CapitalGamma] in coordinates 'chart'.
Limited to tensors of rank no higher than 3 at present.",StandardForm]
LieD::usage = ToString[
"LieD[\[Omega],X,chart,g] returns the covariant derivative of fully covariant tensor \[Omega] in coordinates 'chart' with metric g along vector field X.
LieD[\[Omega],X,chart,g,\[CapitalGamma]] returns the covariant derivative of fully covariant tensor \[Omega] with Chrisoffel symbols \[CapitalGamma] in coordinates 'chart' with metric g along vector field X.
Limited to tensors of rank no higher than 2 at present.",StandardForm]
Riemann::usage = ToString[
"Riemann[g,chart] returns the Riemann tensor \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Alpha]\)], \(\[Beta]\[Gamma]\[Delta]\)]\) for the metric g in coordinates 'chart' assuming torsionless connection (Christoffel symbols).
Riemann[g,chart,\[CapitalGamma]] returns the Riemann tensor \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Alpha]\)], \(\[Beta]\[Gamma]\[Delta]\)]\) for the metric g in coordinates 'chart' with Christoffel symbols \[CapitalGamma]."]
Ricci::usage = ToString[
"Ricci[g,chart] returns the Ricci tensor \!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\) for the metric g in coordinates 'chart' assuming torsionless connection (Christoffel symbols).
Ricci[g,chart,\!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Alpha]\)], \(\[Beta]\[Gamma]\[Delta]\)]\)] returns the Ricci tensor \!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\) for the metric g in coordinates 'chart' from Riemmann tensor \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Alpha]\)], \(\[Beta]\[Gamma]\[Delta]\)]\)."]
RicciS::usage = ToString[
"Ricci[g,chart] returns the Ricci scalar R for the metric g in coordinates 'chart' assuming torsionless connection (Christoffel symbols).
Ricci[g,chart,\!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\)] returns the Ricci scalar R for the metric g in coordinates 'chart' from Ricci tensor \!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\)."]
Einstein::usage = ToString[
"Einstein[g,chart] returns the Einstein tensor \!\(\*SubscriptBox[\(G\), \(\[Alpha]\[Beta]\)]\) for the metric g in coordinates 'chart' assuming torsionless connection (Christoffel symbols).
Einstein[g,chart,\!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\)] returns the Einstein tensor \!\(\*SubscriptBox[\(G\), \(\[Alpha]\[Beta]\)]\) for the metric g in coordinates 'chart' from Ricci tensor \!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\)."]
ProjectionMat::usage = ToString[
"ProjectionMat[map,chart] returns the projection matrix corresponding to the map={\!\(\*SubscriptBox[\(x\), \(i\)]\) \[Rule] ..., ...}"]


Begin["`Private`"];


Differential[X_List]:=Module[{},
	If[!MatchQ[Union[Head/@X], {Symbol}], Message[Differential::invalidCoordinate,X]];
	Symbol["d"<>SymbolName[#]]&/@X
];


Metric[ds2_, X_]:=Module[{dim,ds2metdouble,icounter,jcounter, xds2, res,dX},
dX = Differential[X];
dim = Length[dX];
xds2 = Expand[ds2];
res =
Table[Coefficient[xds2,dX[[icounter]] dX[[jcounter]]]/(2-KroneckerDelta[icounter,jcounter]),
{icounter,dim},{jcounter,dim}];
Simplify[res,TimeConstraint->1]
];


Christoffel[metric_,coordinates_]:=Module[{g=metric,x=coordinates,n=Length@coordinates},
Table[(1/2 \!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Sigma] = 1\), \(n\)]\(\(Inverse[g]\)[\([\[Lambda], \[Sigma]]\)] \((D[g[\([\[Sigma], \[Nu]]\)], x[\([\[Mu]]\)]] + D[g[\([\[Sigma], \[Mu]]\)], x[\([\[Nu]]\)]] - D[g[\([\[Mu], \[Nu]]\)], x[\([\[Sigma]]\)]])\)\)\))//Simplify//Apart,{\[Lambda],1,n},{\[Mu],1,n},{\[Nu],1,n}]
]


CovD[\[Tau]_,coordinates_,christoffel_]:=
Block[{x=coordinates,n=Length@coordinates,\[CapitalGamma]=christoffel,rk=Assuming[\[Tau]\[Element]Reals,TensorRank[\[Tau]]],ind,a},
ind=Table[Subscript[a, i],{i,1,rk}];
Table[D[\[Tau][[Sequence@@ind]],x[[der]]]-Plus@@Table[\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Sigma] = 1\), \(n\)]\((\[CapitalGamma][\([\[Sigma], der, ind[\([j]\)]]\)] \[Tau][\([Sequence @@ ReplacePart[ind, j -> \[Sigma]]]\)])\)\),{j,1,rk}],Evaluate@(Sequence@@Table[{ind[[i]],1,n},{i,1,rk}]),{der,1,n}]
]


LieD[\[Omega]_,X_,coordinates_,metric_,christoffel___]:=
Module[{g=metric,x=coordinates,\[CapitalGamma]={christoffel},n=Length@coordinates,rk=Assuming[\[Omega]\[Element]Reals,TensorRank[\[Omega]]],ind,a},
If[\[CapitalGamma]=={},\[CapitalGamma]=Christoffel[g,x],\[CapitalGamma]=First@\[CapitalGamma]];
ind=Table[Subscript[a, i],{i,1,rk}];
If[
rk==0,\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Sigma] = 1\), \(n\)]\(X[\([\[Sigma]]\)] \(CovD[\[Omega], x, \[CapitalGamma]]\)[\([\[Sigma]]\)]\)\),
Table[\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Sigma] = 1\), \(n\)]\((X[\([\[Sigma]]\)] \(CovD[\[Omega], x, \[CapitalGamma]]\)[\([Sequence @@ Join[ind, {\[Sigma]}]]\)] + Plus @@ Table[
\*SubsuperscriptBox[\(\[Sum]\), \(\[Tau] = 1\), \(n\)]\((\(Inverse[g]\)[\([\[Sigma], \[Tau]]\)] \[Omega][\([Sequence @@ ReplacePart[ind, j -> \[Tau]]]\)] \(CovD[g . X, x, \[CapitalGamma]]\)[\([\[Sigma], ind[\([j]\)]]\)])\), {j, 1, rk}])\)\),Evaluate@(Sequence@@Table[{ind[[i]],1,n},{i,1,rk}])]//Simplify
]
]


Riemann[metric_,coordinates_,christoffel___]:=Module[{g=metric,x=coordinates,n=Length@coordinates,\[CapitalGamma]={christoffel}},
If[\[CapitalGamma]=={},\[CapitalGamma]=Christoffel[g,x],\[CapitalGamma]=First@\[CapitalGamma]];
Table[(D[\[CapitalGamma][[\[Lambda],\[Mu],\[Sigma]]],x[[\[Nu]]]]-D[\[CapitalGamma][[\[Lambda],\[Mu],\[Nu]]],x[[\[Sigma]]]]+\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Eta] = 1\), \(n\)]\(\[CapitalGamma][\([\[Eta], \[Mu], \[Sigma]]\)] \[CapitalGamma][\([\[Lambda], \[Eta], \[Nu]]\)]\)\)-\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Eta] = 1\), \(n\)]\(\[CapitalGamma][\([\[Eta], \[Mu], \[Nu]]\)] \[CapitalGamma][\([\[Lambda], \[Eta], \[Sigma]]\)]\)\))//Simplify,{\[Lambda],1,n},{\[Mu],1,n},{\[Nu],1,n},{\[Sigma],1,n}]
]


Ricci[metric_,coordinates_,riemann___]:=
Module[{g=metric,x=coordinates,n=Length@coordinates,R={riemann}},
If[R=={},R=Riemann[g,x],R=First@R];
Table[(\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(\[Sigma] = 1\), \(n\)]\(R[\([\[Sigma], \[Mu], \[Sigma], \[Nu]]\)]\)\))//Simplify,{\[Mu],1,n},{\[Nu],1,n}]
]


RicciS[metric_,coordinates_,ricci___]:=
Module[{g=metric,x=coordinates,n=Length@coordinates,R={ricci}},
If[R=={},R=Ricci[g,x],R=First@R];
Tr[Inverse[g].R]//Simplify
]


Einstein[metric_,coordinates_,ricci___]:=
Module[{g=metric,x=coordinates,n=Length@coordinates,R={ricci},Rs},
If[R=={},
R=Ricci[g,x];
Rs=RicciS[g,x];
,
R=First@R;
Rs=Tr[Inverse[g].R];
];
R-1/2 g Rs//Simplify
]


ProjectionMat[map_,coordinates_]:=
Module[{dim=Length[map],dim\[CapitalSigma]=Length[coordinates]},
Table[D[map[[i,2]],coordinates[[j]]],{i,1,dim},{j,1,dim\[CapitalSigma]}]
]


End[];
EndPackage[];
