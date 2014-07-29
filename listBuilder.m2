listBuilder = method()
listBuilder(List,ZZ) := (degreeList,deg) -> (
    finished = false;
    listOfPowers = {};
    for i from 0 to (#degreeList-1) do (
	listOfPowers = append(listOfPowers, 0)
	);
    	listOfLists = {};
    while finished == false do (
	print(listOfPowers);
	if (sum(listOfPowers) < deg)
	then (
	    listOfLists = append(listOfLists,listOfPowers)
	    );
	overflowColumn = 0;
	activateOverflow = false;
	if (listOfPowers_0 >= (degreeList_0)-1) 
	then (
	    activateOverflow = true;
	);
    	print(activateOverflow);
	if activateOverflow == false 
	then (
	    tempList = {(listOfPowers_0)+1};
	    for i from 1 to (#listOfPowers-1) do (
		tempList = append(tempList, listOfPowers_i)
		);
	    listOfPowers = tempList;
	    )
	else (
	    overflowLocated = false;
	    while overflowLocated == false do (
		overflowColumn = overflowColumn +1;
		if (overflowColumn >= #listOfPowers) then (overflowLocated = true; finished = true;)
		else(
		    if (listOfPowers_overflowColumn < degreeList_overflowColumn) then (
		    overflowLocated = true)
		);
	    );
	print("hi! ", overflowColumn < #listOfPowers);
	    if (overflowColumn < #listOfPowers) then (
		tempList = {};
		for i from 0 to (overflowColumn-1) do (
		    tempList = append(tempList,0)
		    );
		tempList = append(tempList, (listOfPowers_overflowColumn)+1);
		for i from (overflowColumn+1) to (#listOfPowers-1) do (
		    tempList = append(tempList, listOfPowers_i)
		);
	    	listOfPowers = tempList;
	    );
	);
    );
listOfLists
)


end
restart
load "listBuilder.m2"
listBuilder({3,2,3},10)
