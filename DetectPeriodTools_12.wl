(* ::Package:: *)

(* ::Input::Initialization:: *)
PointApplyRule[rule_,init_]:=CellularAutomaton[rule, init, 1][[2,(Length[init]+1)/2]]


RunCA[rule_, init_List, steps_]:=CellularAutomaton[rule, {init, 0}, steps]
RunCA[rule_, init_Integer, steps_]:=RunCA[rule, IntegerDigits[init, AnalyzeRule[rule]["Colors"]], steps]


(* ::Input::Initialization:: *)
AnalyzeRule[{n_, {k_, 1}, r_}]:=AnalyzeRule[{n, {k, 1}, r}]=Module[{rule={n, {k, 1}, r},minimumtolerablegap=2r+1},
While[AllTrue[Tuples[Range[k]-1, 2r+2-minimumtolerablegap], PointApplyRule[rule, PadLeft[#, 2r+1]]==0&], minimumtolerablegap--];
<|"Rule"->rule, "Colors"->k, "Totalistic"->True, "Number"->n, "Radius"->r, "MinimumTolerableGap"->minimumtolerablegap|>
]
AnalyzeRule[{n_, k_, r_}]:=AnalyzeRule[{n, k, r}]=Module[{rule={n,k, r},minimumtolerablegap=2r+1},
While[AllTrue[Tuples[{0, 1}, 2r+2-minimumtolerablegap], PointApplyRule[rule, PadLeft[#, 2r+1]]==0&], minimumtolerablegap--];
<|"Rule"->rule, "Colors"->k, "Totalistic"->True, "Number"->n,"Radius"->r, "MinimumTolerableGap"->minimumtolerablegap|>
]
AnalyzeRule[{n_, k_}]:=AnalyzeRule[{n, k, 1}]
AnalyzeRule[{n_}]:=AnalyzeRule[{n, 2}]
AnalyzeRule[n_]:=AnalyzeRule[{n}]


(* ::Input::Initialization:: *)
AllZeros=FunctionCompile[Function[Typed[list,"PackedArray"::["MachineInteger", 1]], Module[{i=Length[list]}, While[i>0&&list[[i]]==0, i--;]; i==0]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3,"InvocationMode"->"Standalone"}];


(* ::Input::Initialization:: *)
StripZeros=FunctionCompile[Function[Typed[list, "PackedArray"::["MachineInteger", 1]],Module[
{i=1, j=Length[list]},
If[
(* AllZeros *)
Module[{i0=Length[list]}, While[i0>0&&list[[i0]]==0, i0--;]; i0==0],
 Return[Table[0, {iter, 0}]]
];
While[list[[i]]==0, i++];
 While[list[[j]]==0, j--]; 
list[[i;;j]]
]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3,"InvocationMode"->"Standalone"}];


(* ::Input::Initialization:: *)
MaxGapLength=FunctionCompile[Function[Typed[list, "PackedArray"::["MachineInteger", 1]],Module[
{currentlen=0, maxlen=0},
Do[currentlen=If[i==0, currentlen+1,0]; 
maxlen=Max[maxlen, currentlen];, {i,list}];
maxlen
]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3,"InvocationMode"->"Standalone"}];


(* ::Input::Initialization:: *)
FindRepeatDeterministic[list_List]:=
list[[-First[FirstPosition[Reverse[list[[;;-2]]], list[[-1]], {0}]];;]]


(* ::Input::Initialization:: *)
FindRepeatDeterministicIndexByStripZerosCompiled=FunctionCompile[Function[Typed[list,"PackedArray"::["MachineInteger", 2]],
With[{StripZeros=Function[Typed[list2, "PackedArray"::["MachineInteger", 1]],Module[
{i=1, j=Length[list2]},
While[list2[[i]]==0&&i<j, i++];
 If[i<j,While[list2[[j]]==0, j--]]; 
If[i==j,Table[0, 0],list2[[i;;j]]]]
]},
Module[{i=Length[list]-1, last=StripZeros[list[[-1]]]},
 While[i>0&&StripZeros[list[[i]]]!=last, i--]; If[i==0, 0,i+1]
]]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3}];

FindRepeatDeterministicByStripZeros[list_List]:=StripZeros/@list[[FindRepeatDeterministicIndexByStripZerosCompiled[list];;]]


(* ::Input::Initialization:: *)
DedupSamePass1[associations_, parameter_:"Canonical"]:=Union[associations,SameTest->(#1[parameter]==#2[parameter]&)]

DedupSamePass2[associations_, steps_Integer:300]:=Module[{found=CreateDataStructure["HashSet"], out={}, carun, ra}, Do[
carun=RunCA[soln["Rule"], soln["Canonical"], steps];
carun=StripZeros/@carun;
carun=Union[carun];
ra=AnalyzeRule[soln["Rule"]];
If[AllTrue[carun, found["Insert", FromDigits[StripZeros[#], ra["Colors"]]]&], AppendTo[out, soln]]
, {soln, associations}]; out]

DedupSame[associations_, parameter_String:"Canonical", steps_Integer:300]:=SortBy[SortBy[DedupSamePass2[DedupSamePass1[associations, parameter], steps], #Canonical&], #Period&]


(* ::Input::Initialization:: *)
DedupSamePass1[associations_, parameter_:"Canonical"]:=Union[associations,SameTest->(#1[parameter]==#2[parameter]&)]

DedupSamePass2[associations_, steps_Integer:300]:=Module[{found=CreateDataStructure["HashSet"], out={}, carun, ra}, Do[
carun=RunCA[soln["Rule"], soln["Canonical"], steps];
carun=StripZeros/@carun;
carun=Union[carun];
ra=AnalyzeRule[soln["Rule"]];
If[AllTrue[carun, found["Insert", FromDigits[StripZeros[#], ra["Colors"]]]&], AppendTo[out, soln]]
, {soln, associations}]; out]

DedupSame[associations_, parameter_String:"Canonical", steps_Integer:300]:=SortBy[SortBy[DedupSamePass2[DedupSamePass1[associations, parameter], steps], #Canonical&], #Period&]


(* ::Input::Initialization:: *)
Clear[SplitSeparateSolutions];
data={};
SplitSeparateSolutions[carun_, mtg_]:=Module[{mask, mc, colors, carunpadded},
AppendTo[data, carun];
carunpadded=PadLeft[carun, {Length[carun], Length[carun[[-1]]]+mtg}];
mask=Sum[carunpadded[[All,i;;(i-mtg-1)]], {i, mtg}];
mc=Last[MorphologicalComponents[Image[mask], CornerNeighbors->False]];
colors=Union[mc];
Select[Table[StripZeros[(1-Unitize[c-mc[[2;;]]])*carun[[-1]]], {c, colors}], Not@*AllZeros]
]


(* ::Input::Initialization:: *)
Clear[SplitSeparateSolutions2];
SplitSeparateSolutions2[carun_, rule_]:=Module[{encounteredNonzero=False, first=First[carun], w,superposition, left, right, result=None},
w=Length[first];
Do[
encounteredNonzero=Or[encounteredNonzero, first[[i]]!=0];
If[encounteredNonzero&&first[[i]]==0,
left=CellularAutomaton[rule, ArrayPad[PadRight[first[[;;i]], w], 2], Length[carun]-1];
right=CellularAutomaton[rule,ArrayPad[PadLeft[first[[i;;]], w], 2], Length[carun]-1];
(* Print[ArrayPlot[left], ArrayPlot[right], ArrayPlot[left+right], ArrayPlot[carun]]; *)

superposition=(left+right)[[All, 3;;-3]];

If[superposition==carun&&!AllZeros[Last[left]]&&!AllZeros[Last[right]], 

result=Join[
{StripZeros[Last[left]]},
SplitSeparateSolutions2[right, rule]
];

Break[];
];

encounteredNonzero=False;
];
,{i, w}];

If[result===None, {StripZeros[Last[carun]]}/.{}->Nothing, result]
]


(* ::Input::Initialization:: *)
Clear[AArrayPlot];
AArrayPlot[rule_, init_List, steps_Integer:100,ops:OptionsPattern[ArrayPlot]]:=ArrayPlot[RunCA[rule, init, steps], {ops}]
AArrayPlot[rule_, init_Integer, args___]:=AArrayPlot[rule, IntegerDigits[init, AnalyzeRule[rule]["Colors"]], args]


(* ::Input::Initialization:: *)
Clear[VisualizeDetectPeriod];
Clear[MultiVisualizeDetectPeriod];
VisualizeDetectPeriod[rule_, init_, stepsog_:None, ops:OptionsPattern[ArrayPlot]]:=Module[{results, steps},
results=DetectPeriod[rule, init];
steps=If[stepsog===None, Min[1000, Max[results[[All, "MaxSteps"]], 0]], stepsog];

Row[{
Labeled[AArrayPlot[rule, init, steps, {ops}], ClickToCopy["Orig", results]],
Row[
Labeled[
AArrayPlot[rule,#Canonical, 5+(3*#Period/.(0->2*steps)),{Mesh->#Period!=0,ops}],ClickToCopy[
#Period/.(0->"None"), #Canonical]]&
/@DedupSame[results]
]
}]
]
MultiVisualizeDetectPeriod[rule_, inits_, args___]:=Column[ParallelTable[VisualizeDetectPeriod[rule, init, args], {init, inits}]]


(* ::Input::Initialization:: *)
Clear[DetectPeriod];
Clear[DetectPeriodSub];
DetectPeriod[rule_, n_Integer, args___]:=DetectPeriod[rule, IntegerDigits[n, AnalyzeRule[rule]["Colors"]], args]
DetectPeriod[rule_, list_List, steps_Integer:200, maxdepth_Integer:20]:=With[{ra=AnalyzeRule[rule]}, {res=DetectPeriodSub[ra, list, steps, maxdepth]},Join[<|"Rule"->rule,"Canonical"->FromDigits[list, ra["Colors"]], "Original"->FromDigits[list, ra["Colors"]], "IsGliderGun"->False, "MaxDepth"->maxdepth-#LowestDepth, "MaxSteps"->steps*(2^(1+maxdepth-#LowestDepth)-1)|>, #]&/@res];

DetectPeriodSub[ra_, list_, steps_, ogmaxdepth_]:=Module[
{carun, frd, separatesolutions, period, canonical, shift, maxdepth},
maxdepth=ogmaxdepth;

Assert[maxdepth>=0];

carun=RunCA[ra["Rule"], list, steps];

(* If it dies, return *);
If[AllZeros[carun[[-1]]], Return[{}]];

(* Detect Periodicity *)
frd=FindRepeatDeterministicByStripZeros[carun];

If[ByteCount[carun]>8000000, maxdepth=Min[maxdepth, 2]];

If[maxdepth<=1,If[Length[frd]==0,
Return[{<|"Period"->0, "IsGliderGun"->True, "LowestDepth"->maxdepth|>}],
Return[{<|"Period"->Length[frd],"Canonical"->Min[Min[FromDigits[#,ra["Colors"]]&/@frd], Min[FromDigits[Reverse[#],ra["Colors"]]&/@frd]], "LowestDepth"->maxdepth|>}];
]];

(* If unfinished and probably unseparated, recurse with more steps *);
If[Length[frd]==0, 
Return[If[MaxGapLength[carun[[-1]]]>15,
separatesolutions=SplitSeparateSolutions2[carun, ra["Rule"]];
Join@@Table[
DetectPeriodSub[ra, subsolution, steps, maxdepth-1],
 {subsolution, separatesolutions}
],
DetectPeriodSub[ra, carun[[-1]], 2 * steps, maxdepth - 1]
]]
];

(* Otherwise, run again for pure periodicity *)
carun=RunCA[ra["Rule"], carun[[-1]], steps];

(* If it's multiperiodic, split solutions *);
separatesolutions=SplitSeparateSolutions2[RunCA[ra["Rule"], carun[[-Length[frd]]], 2*Length[frd]], ra["Rule"]];
(*separatesolutions= SortBy[separatesolutions,First[FirstPosition[#, 1, 0]]&] *);

(* Recurse on each subsolution, if they exist *);
If[Length[separatesolutions]>1,
Return[Join@@Table[
DetectPeriodSub[ra, subsolution, steps, maxdepth-1],
 {subsolution, separatesolutions}
]]
];

(* Return single-solution period *);
period=Length[frd];
canonical=Min[Min[FromDigits[#,ra["Colors"]]&/@frd], Min[FromDigits[Reverse[#],ra["Colors"]]&/@frd]];
carun=RunCA[ra["Rule"],IntegerDigits[canonical, ra["Colors"]], period];

shift=FromDigits[Last[carun], ra["Colors"]];
If[shift!=0, shift=Log[ra["Colors"],FromDigits[First[carun], ra["Colors"]]/shift]];

Return[{<|"Period"->period,"Canonical"->canonical, "Shift"->shift, "LowestDepth"->maxdepth|>}];
]
