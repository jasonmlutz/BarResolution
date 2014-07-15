--Returns the digits in nn which are nonzero in binary 
--for example, 5 in binary is 101, so this would return {0,2}
--the second term tells me where to start the count, so passing
--5,0 gives {0,2} but 5,1 is sent to {1,3}.  i=!=0 should be
--used only for recursive purposes
getNonzeroBinaryDigits = (nn, i) -> (
--    error "breakme";
    halfsies := nn//2;
    val1 := nn%2;
    val2 := false; 
    if (halfsies > 0) then val2 = (getNonzeroBinaryDigits(nn//2,i+1));
    if ( (val1 != 0) and (not (val2 === false))) then (
	 flatten {i, val2}
    )
    else if (val1 != 0) then (
	 {i}
    )
    else if ( not (val2 === false)) then (
	 flatten {val2}
    )
    else(
	 false
    )
)

--Returns the entries of myList specified by entryList
--For example, ( {1,2,3}, {0,2}) is sent to {1,3}
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)

--Returns the power set of a given list, leaving out the emptyset.  
--E.g. {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
--as applied to cleverFactor, nontrivialPowerSet will help index all possible
--candidates for the set A over which the sum is indexed.
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)

specialPartial = (myPolynomial,varsList) -> (
       
)

cleverFactor = method()
cleverFactor := (f) -> (
    myRing := ring f;
    if not isHomogeneous f
    then error "expected a polynomial ring over a field";
    myField := myRing.baseRings // last; --more efficient
    if not (isField myField)
    then error "expected a polynomial ring over a field";
    if (char R) =!= 0
    then error "expected a characteristic 0 base field";
    numVars := length gens myRing;
    newGens = gens myRing;
    for i from 1 to numVars do (
    	newGens = append(newGens, y_i);
    );
    myNewRing := newRing(myRing, Variables=>newGens);
    XGens = {};
    YGens = {};
    for i from 1 to numVars do (
	XGens=append(XGens, (gens myNewRing)_(i-1));
	YGens=append(YGens, (gens myNewRing)_((numVars)+i-1));
    );	    
    injX := map(myNewRing, myRing, matrix{XGens});
    injY := map(myNewRing, myRing, matrix{YGens});
    fx := injX(f);
    fy := injY(f);
    deg := degree f;
    coefficientMatrix = mutableMatrix(myNewRing, 1, numVars);
    for columnCount from 1 to numVars do (
	--columnCount tracks the variable pair x_j-y_j
	varsIndices = 1..numVars; --a sequence
    	varsIndices = toList indexedVars; --now a list
    	indicesSubset = nontrivialPowerSet(varsIndices);
	for subsetCounter from 1 to 2^(numVars-1) do (
	    varsSubset = indicesSubset_subsetCounter;
	    if isSubset(set{columnCount},varsSubset) then
	    for j in varsSubset do (
		varFactor = 1;
		for a in varsSubset do (
		    if a=!=columnCount then varFactor = varFactor*XGens_(a-1)
		);
    	    	coefficientMatrix_(0,columnCount) = (1/d^(# varsSubset))*varFactor*specialPartial(fy,yVarsSubset);
		);
	);
    );
coefficientMatrix

)




end
restart
load "cleverFactor.m2"
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
