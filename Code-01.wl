(* ::Package:: *)

(* ::Input::Initialization:: *)
PointApplyRule[rule_,init_]:=CellularAutomaton[rule, init, 1][[2,(Length[init]+1)/2]]


(* ::Input::Initialization:: *)
AnalyzeRule[{n_, {k_, 1}, r_}]:=AnalyzeRule[{n, {k, 1}, r}]=Module[{rule={n, {k, 1}, r},minimumtolerablegap=2r+1},
While[AllTrue[Tuples[Range[k]-1, 2r+2-minimumtolerablegap], PointApplyRule[rule, PadLeft[#, 2r+1]]==0&], minimumtolerablegap--];
<|"Rule"->rule, "Colors"->k, "Totalistic"->True, "Radius"->r, "MinimumTolerableGap"->minimumtolerablegap|>
]
AnalyzeRule[{n_, k_, r_}]:=AnalyzeRule[{n, k, r}]=Module[{rule={n,k, r},minimumtolerablegap=2r+1},
While[AllTrue[Tuples[{0, 1}, 2r+2-minimumtolerablegap], PointApplyRule[rule, PadLeft[#, 2r+1]]==0&], minimumtolerablegap--];
<|"Rule"->rule, "Colors"->k, "Totalistic"->True, "Radius"->r, "MinimumTolerableGap"->minimumtolerablegap|>
]
AnalyzeRule[{n_, k_}]:=AnalyzeRule[{n, k, 1}]
AnalyzeRule[{n_}]:=AnalyzeRule[{n, 2}]
AnalyzeRule[n_]:=AnalyzeRule[{n}]

Timing[AnalyzeRule[{20, {2, 1}, 2}]]
AnalyzeRule[{2, {2, 1}, 2}]
AnalyzeRule[{32, {2, 1}, 2}]
AnalyzeRule[30]
RepeatedTiming[AnalyzeRule[{20, {2, 1}, 2}]]


(* ::Input::Initialization:: *)
CloseKernels[];
LaunchKernels[];


(* ::Input::Initialization:: *)
Clear[AArrayPlot];
AArrayPlot[rule_, init_List, steps_Integer:100, meshQ:_?BooleanQ:True, ops:OptionsPattern[ArrayPlot]]:=ArrayPlot[RunCA[rule, init, steps], Mesh->meshQ,ops]
AArrayPlot[rule_,init_Integer, args___]:=AArrayPlot[rule, IntegerDigits[init, AnalyzeRule[rule]["Colors"]], args]

AArrayPlot[rule_][init_List, args___]:=AArrayPlot[rule, init, args]
AArrayPlot[rule_, args___][init_Integer]:=AArrayPlot[rule, init, args]
AArrayPlot[rule_][init_List, args___]:=AArrayPlot[rule, init, args]
AArrayPlot[rule_, args___][init_Integer]:=AArrayPlot[rule, init, args]


(* ::Input::Initialization:: *)
code20rule={20, {2, 1}, 2};
RunCA[rule_, init_, steps_]:=(mostrecentlyusedrule=rule;CellularAutomaton[rule, {init, 0}, steps])
RunCode20[init_, steps_]:=RunCA[code20rule, init, steps]


(* ::Input::Initialization:: *)
AllZeros=FunctionCompile[Function[Typed[list,"PackedArray"::["MachineInteger", 1]], Module[{i=Length[list]}, While[i>0&&list[[i]]==0, i--;]; i==0]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3,"InvocationMode"->"Standalone"}];
RepeatedTiming[AllZeros[{0, 0, 0, 0, 1, 0}]]
RepeatedTiming[Max[{0, 0, 0, 0, 1, 0}]==0]


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

RepeatedTiming[StripZeros[RandomInteger[{0, 1}, 1000]]]//First
StripZeros[{0, 0, 0, 0,0}]


(* ::Input::Initialization:: *)
MaxGapLength=FunctionCompile[Function[Typed[list, "PackedArray"::["MachineInteger", 1]],Module[
{currentlen=0, maxlen=0},
Do[currentlen=If[i==0, currentlen+1,0]; 
maxlen=Max[maxlen, currentlen];, {i,list}];
maxlen
]], CompilerOptions->{"LLVMOptimization"->"ClangOptimization"[3], "AbortHandling"->False, "OptimizationLevel"->3,"InvocationMode"->"Standalone"}];
RepeatedTiming[MaxGapLength[RandomInteger[{0, 1}, 1000]]]


(* ::Input::Initialization:: *)
FindRepeatDeterministic[list_]:=
list[[-First[FirstPosition[Reverse[list[[;;-2]]], list[[-1]], {0}]];;]]


(* ::Input::Initialization:: *)
Clear[SplitSeparateSolutions];
SplitSeparateSolutions[carun_, mtg_]:=Module[{mask, mc, colors, carunpadded},
carunpadded=PadLeft[carun, {Length[carun], Length[carun[[-1]]]+mtg}];
mask=Sum[carunpadded[[All,i;;(i-mtg-1)]], {i, mtg}];
mc=Last[MorphologicalComponents[Image[mask], CornerNeighbors->False]];
colors=Union[mc];
Select[Table[(1-Unitize[c-mc[[2;;]]])*carun[[-1]], {c, colors}], Not@*AllZeros]
]

SplitSeparateSolutions[RunCode20[IntegerDigits[233 + 2^14 * 151, 2], 100], 4]
SplitSeparateSolutions[RunCode20[IntegerDigits[12555286547204781505564672, 2], 100], 4]
First@RepeatedTiming[SplitSeparateSolutions[RunCode20[IntegerDigits[12555286547204781505564672, 2], 100], 4]]


(* ::Input::Initialization:: *)
Clear[DetectPeriod];
DetectPeriod[rule_, n_Integer, args___]:=DetectPeriod[rule, IntegerDigits[n, AnalyzeRule[rule]["Colors"]], args]
DetectPeriod[rule_, list_List, steps_:200, maxdepth_:20]:=With[{ra=AnalyzeRule[rule]}, {res=DetectPeriodSub[ra, list, steps, maxdepth]},Join[<|"Rule"->rule,"Canonical"->FromDigits[list, ra["Colors"]], "Original"->FromDigits[list, ra["Colors"]], "MaxDepth"->maxdepth-#LowestDepth, "MaxSteps"->steps*(2^(1+maxdepth-#LowestDepth)-1)|>, #]&/@res];

DetectPeriodSub[ra_, list_, steps_, ogmaxdepth_]:=Module[
{carun, frd, separatesolutions, period, canonical, shift, maxdepth},
maxdepth=ogmaxdepth;

If[maxdepth<0,
Print["Something Went Wrong."];
];

carun=RunCA[ra["Rule"], list, steps];


If[ByteCount[carun]>800000, maxdepth=Min[maxdepth, 1]];

(* If it dies, return *);
If[AllZeros[carun[[-1]]], Return[{}]];

(* Detect Periodicity *)
frd=FindRepeatDeterministic[StripZeros/@carun];

If[maxdepth<=0,If[Length[frd]==0,
Return[{<|"Period"->0, "IsGliderGun"->True, "LowestDepth"->maxdepth|>}],
Return[{<|"Period"->Length[frd],"Canonical"->Min[Min[FromDigits[StripZeros[#],ra["Colors"]]&/@frd], Min[FromDigits[Reverse[StripZeros[#]],ra["Colors"]]&/@frd]], "IsUnfinished"->True, "LowestDepth"->maxdepth|>}];
]];

(* If unfinished and probably unseparated, recurse with more steps *);
If[Length[frd]==0, 
Return[If[MaxGapLength[carun[[-1]]]>15,
separatesolutions=SplitSeparateSolutions[carun, ra["MinimumTolerableGap"]];
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
separatesolutions=SplitSeparateSolutions[carun[[-Length[frd];;]], ra["MinimumTolerableGap"]];
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
canonical=Min[Min[FromDigits[StripZeros[#],ra["Colors"]]&/@frd], Min[FromDigits[StripZeros[Reverse[#]],ra["Colors"]]&/@frd]];
carun=RunCA[ra["Rule"],IntegerDigits[canonical, ra["Colors"]], period];
shift=Log[ra["Colors"],FromDigits[First[carun], ra["Colors"]]/FromDigits[Last[carun], ra["Colors"]]];

Return[{<|"Period"->period,"Canonical"->canonical, "Shift"->shift, "LowestDepth"->maxdepth|>}];
]


(* ::Input::Initialization:: *)
code1329rule={1329,{3,1},1};
RunCode1329[init_, steps_]:=RunCA[code1329rule, init, steps]
IRunCode1329[n_, steps_]:=RunCode1329[IntegerDigits[n, 3], steps]


(* ::Input::Initialization:: *)
DedupSame[associations_, parameter_:"Canonical"]:=Union[associations,SameTest->(#1[parameter]==#2[parameter]&)]


(* ::Input::Initialization:: *)
VisualizeDetectPeriod[rule_, init_, stepsog_:None, ops:OptionsPattern[{ArrayPlot}]]:=Module[{results, steps},
results=DetectPeriod[rule, init];
steps=If[stepsog===None, Min[1000, Max[results[[All, "MaxSteps"]]]], stepsog];

Row[{
ClickToCopy[AArrayPlot[rule, init, steps, False], results],
Row[
ClickToCopy[Labeled[
AArrayPlot[rule,#Canonical, 2*#Period/.(0->2*steps), #Period!=0]
, #Period/.(0->"None")], #Canonical]&
/@results
]
}]
]
MultiVisualizeDetectPeriod[rule_, inits_, args___]:=Column[ParallelTable[VisualizeDetectPeriod[rule, init, args], {init, inits}]]
