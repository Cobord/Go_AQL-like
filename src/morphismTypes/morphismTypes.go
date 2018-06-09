package morphismTypes

import "reflect"

func presentInts(myInts []int) map[int]bool {
	var myIntMap map[int]bool
	for _, currentInt := range myInts {
		myIntMap[currentInt] = true
	}
	return myIntMap
}

type myFunction struct {
	myUnderlyingFunction func(int) int
}

type myFunctionParameterized struct {
	myParams             []string
	myUnderlyingFunction func(int, []interface{}) int
}

func (parameterized *myFunctionParameterized) specializeParams(args []interface{}) (myFunction, bool) {
	if len(parameterized.myParams) != len(args) {
		return myFunction{}, false
	}
	success := true
	for i, v := range parameterized.myParams {
		success = reflect.TypeOf(args[i]).String() == v
		if !success {
			return myFunction{}, false
		}
	}
	return myFunction{myUnderlyingFunction: func(x int) int { return parameterized.myUnderlyingFunction(x, args) }}, true
}

type myPartialFunction struct {
	// if do i, ok = myDomain[x]: this can be true, true for things in the source and domain
	// false, true for things in source but not defined for this map, false, false for things not even in source
	myDomain             map[int]bool
	myUnderlyingFunction func(int) int
}

type myPartialFunctionParameterized struct {
	myParams             []string
	myDomain             map[int]bool
	myUnderlyingFunction func(int, []interface{}) int
}

func (parameterized *myPartialFunctionParameterized) specializeParams(args []interface{}) (myPartialFunction, bool) {
	if len(parameterized.myParams) != len(args) {
		return myPartialFunction{}, false
	}
	success := true
	for i, v := range parameterized.myParams {
		success = reflect.TypeOf(args[i]).String() == v
		if !success {
			return myPartialFunction{}, false
		}
	}
	return myPartialFunction{myDomain: parameterized.myDomain, myUnderlyingFunction: func(x int) int { return parameterized.myUnderlyingFunction(x, args) }}, true
}

type myRelation struct {
	myUnderlyingFunction func(int) []int
}

type myRelationParameterized struct {
	myParams             []string
	myUnderlyingFunction func(int, []interface{}) []int
}

func (parameterized *myRelationParameterized) specializeParams(args []interface{}) (myRelation, bool) {
	if len(parameterized.myParams) != len(args) {
		return myRelation{}, false
	}
	success := true
	for i, v := range parameterized.myParams {
		success = reflect.TypeOf(args[i]).String() == v
		if !success {
			return myRelation{}, false
		}
	}
	return myRelation{myUnderlyingFunction: func(x int) []int { return parameterized.myUnderlyingFunction(x, args) }}, true
}

type possiblyRelation interface {
	CastToRelation(domain []int) myRelation
}

type possiblyPartialFunction interface {
	CastToPartialFunction(domain []int) myPartialFunction
	possiblyRelation
}

func castFToPF(f myFunction, domain []int) myPartialFunction {
	myDomain2 := presentInts(domain)
	return myPartialFunction{myDomain: myDomain2, myUnderlyingFunction: f.myUnderlyingFunction}
}

func castFToR(f myFunction, domain []int) myRelation {
	var toReturn map[int]([]int)
	for _, currentInt := range domain {
		toReturn[currentInt] = append(toReturn[currentInt], f.myUnderlyingFunction(currentInt))
	}
	return myRelation{myUnderlyingFunction: func(x int) []int { return toReturn[x] }}
}
func castPFToR(f myPartialFunction, domain []int) myRelation {
	toReturn := make(map[int]([]int))
	for _, currentInt := range domain {
		if f.myDomain[currentInt] {
			toReturn[currentInt] = append(toReturn[currentInt], f.myUnderlyingFunction(currentInt))
		}
	}
	return myRelation{myUnderlyingFunction: func(x int) []int { return toReturn[x] }}
}

func (f myFunction) CastToPartialFunction(domain []int) myPartialFunction {
	return castFToPF(f, domain)
}

func (f myFunction) CastToRelation(domain []int) myRelation {
	return castFToR(f, domain)
}

func (f myPartialFunction) CastToPartialFunction(domain []int) myPartialFunction {
	return f
}

func (f myPartialFunction) CastToRelation(domain []int) myRelation {
	return castPFToR(f, domain)
}

func (f myRelation) CastToRelation(domain []int) myRelation {
	return f
}

func (f myRelation) ReverseRelation(source []int, target []int) myRelation {
	var gottenI []int
	toReturn := make(map[int]([]int))
	for _, i := range source {
		gottenI = f.myUnderlyingFunction(i)
		for _, j := range gottenI {
			// could check if j is in target here
			toReturn[j] = append(toReturn[j], i)
		}
	}
	return myRelation{myUnderlyingFunction: func(x int) []int { return toReturn[x] }}
}

func composeFunctions(f1, f2 myFunction, domain1, domain2 []int) myFunction {
	return myFunction{myUnderlyingFunction: func(x int) int { return f2.myUnderlyingFunction(f1.myUnderlyingFunction(x)) }}
}

func composeManyFunctions(fList []myFunction, domainList [][]int) (myFunction, bool) {
	fListLength := len(fList)
	domainListLength := len(domainList)
	if fListLength != domainListLength {
		return myFunction{}, false
	}
	if fListLength == 1 {
		return fList[0], true
	} else {
		f1 := fList[0]
		domain1 := domainList[0]
		f2, _ := composeManyFunctions(fList[1:], domainList[1:])
		domain2 := domainList[1]
		return composeFunctions(f1, f2, domain1, domain2), true
	}
}

func composePartials(f1, f2 possiblyPartialFunction, domain1, domain2 []int) myPartialFunction {
	f1Partialized := f1.CastToPartialFunction(domain1)
	f2Partialized := f2.CastToPartialFunction(domain2)
	var afterf1 int
	//combine f1Partialized and f2Partialized
	modifiedDomain := make(map[int]bool, len(f1Partialized.myDomain))
	for key, value := range f1Partialized.myDomain {
		if value {
			afterf1 = f1Partialized.myUnderlyingFunction(key)
			if f2Partialized.myDomain[afterf1] {
				modifiedDomain[key] = true
			}
		}
	}
	return myPartialFunction{myDomain: modifiedDomain, myUnderlyingFunction: func(x int) int { return f2Partialized.myUnderlyingFunction(f1Partialized.myUnderlyingFunction(x)) }}
}

func composeManyPartials(fList []possiblyPartialFunction, domainList [][]int) (myPartialFunction, bool) {
	fListLength := len(fList)
	domainListLength := len(domainList)
	if fListLength != domainListLength {
		return myPartialFunction{}, false
	}
	if fListLength == 1 {
		return fList[0].CastToPartialFunction(domainList[0]), true
	} else {
		f1 := fList[0]
		domain1 := domainList[0]
		f2, _ := composeManyPartials(fList[1:], domainList[1:])
		domain2 := domainList[1]
		return composePartials(f1, f2, domain1, domain2), true
	}
}

func composeRelations(f1, f2 possiblyRelation, domain1, domain2 []int) myRelation {
	f1Relationalized := f1.CastToRelation(domain1)
	f2Relationalized := f2.CastToRelation(domain2)
	//combine f1Partialized and f2Partialized
	return myRelation{myUnderlyingFunction: func(x int) []int {
		toReturn := make([]int, 0)
		for y := range f1Relationalized.myUnderlyingFunction(x) {
			toReturn = append(toReturn, f2Relationalized.myUnderlyingFunction(y)...)
		}
		return removeDuplicates(toReturn)
	}}
}

func removeDuplicates(elements []int) []int {
	// Use map to record duplicates as we find them.
	encountered := map[int]bool{}
	result := []int{}

	for v := range elements {
		if encountered[elements[v]] == true {
			// Do not add duplicate.
		} else {
			// Record this element as an encountered element.
			encountered[elements[v]] = true
			// Append to result slice.
			result = append(result, elements[v])
		}
	}
	// Return the new slice.
	return result
}

func composeManyRelations(fList []possiblyRelation, domainList [][]int) (myRelation, bool) {
	fListLength := len(fList)
	domainListLength := len(domainList)
	if fListLength != domainListLength {
		return myRelation{}, false
	}
	if fListLength == 1 {
		return fList[0].CastToRelation(domainList[0]), true
	} else {
		f1 := fList[0]
		domain1 := domainList[0]
		f2, _ := composeManyRelations(fList[1:], domainList[1:])
		domain2 := domainList[1]
		return composeRelations(f1, f2, domain1, domain2), true
	}
}
