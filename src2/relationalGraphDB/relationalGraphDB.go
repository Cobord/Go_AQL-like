package relationalGraphDB

import "fmt"
import cgs "RelationalGraphDB/src/coloredGraphSchema"
import homs "RelationalGraphDB/src/morphismTypes"

type InstantiatedDB struct {
	underlyingGraph            cgs.SchemaGraph
	underlyingSets             map[cgs.Vertex]([]int)
	underlyingFunctions        map[cgs.FunctionEdge](homs.myFunction)
	underlyingPartialFunctions map[cgs.PartialFunctionEdge](homs.myPartialFunction)
	underlyingRelations        map[cgs.RelationEdge](homs.myRelation)
}

func validateDB(potentialDB InstantiatedDB) bool {
	result := true
	result = cgs.validateGraph(potentialDB.underlyingGraph)
	if !result {
		fmt.Printf("The schema was bad")
		return False
	}
	result = validateFunctions(potentialDB)
	if !result {
		fmt.Printf("The functions were bad")
		return False
	}
	result = validatePartialFunctions(potentialDB)
	if !result {
		fmt.Printf("The partial functions were bad")
		return False
	}
	result = validateRelations(potentialDB)
	if !result {
		fmt.Printf("The relations were bad")
		return False
	}
	result = validateFunctionEquations(potentialDB)
	if !result {
		fmt.Printf("The function equations were bad")
		return False
	}
	result = validatePartialFunctionEquations(potentialDB)
	if !result {
		fmt.Printf("The partial function equations were bad")
		return False
	}
	result = validateRelationEquations(potentialDB)
	if !result {
		fmt.Printf("The relation equations were bad")
		return False
	}
	return result
}

// all the functions should have the property that when inputing a item from the proported source
// you do get a member of the proported target
func validateFunctions(potentialDB InstantiatedDB) bool {
	myFunctionEdges := potentialDB.underlyingGraph.functionEdges
	myVertices := potentialDB.underlyingGraph.vertices
	myVerticesSets := potentialDB.underlyingSets
	myFunctions := potentialDB.underlyingFunctions
	result := true
	for index, edge := range myFunctionEdges {
		sourceVertex := edge.source
		targetVertex := edge.target
		sourceSet := myVerticesSets[sourceVertex]
		targetSet := myVerticesSets[targetVertex]
		currentFunction := myFunctions[edge]
		result = homs.validateFunction(sourceSet, targetSet, currentFunction)
		if !result {
			return false
		}
	}
	return result
}

// all the functions should have the property that when inputing a item from the proported source
// which is well defined according to the partial's domain
// you do get a member of the proported target
func validatePartialFunctions(potentialDB InstantiatedDB) bool {
	myPartialFunctionEdges := potentialDB.underlyingGraph.partialFunctionEdges
	myVertices := potentialDB.underlyingGraph.vertices
	myVerticesSets := potentialDB.underlyingSets
	myPartialFunctions := potentialDB.underlyingPartialFunctions
	result := true
	for index, edge := range myPartialFunctionEdges {
		currentPartialFunction := myPartialFunctions[edge]
		sourceVertex := edge.source
		targetVertex := edge.target
		sourceSet := myVerticesSets[sourceVertex]
		targetSet := myVerticesSets[targetVertex]
		result = homs.validatePartialFunction(sourceSet, targetSet, currentPartialFunction)
		if !result {
			return false
		}
	}
	return result
}

// all the functions should have the property that when inputing a item from the proported source
// every t that gets outputed with (s,t1) ... (s,tn) as [t1...tn]
// all of them should be in the proported target
func validateRelations(potentialDB InstantiatedDB) bool {
	myRelationEdges := potentialDB.underlyingGraph.RelationEdges
	myVertices := potentialDB.underlyingGraph.vertices
	myVerticesSets := potentialDB.underlyingSets
	myRelations := potentialDB.underlyingRelations
	result := true
	for index, edge := range myRelationEdges {
		currentRelation := myRelations[edge]
		sourceVertex := edge.source
		targetVertex := edge.target
		sourceSet := myVerticesSets[sourceVertex]
		targetSet := myVerticesSets[targetVertex]
		result = homs.validateRelation(sourceSet, targetSet, currentRelation)
		if !result {
			return false
		}
	}
	return result
}

// not done yet
func validateFunctionEquations(potentialDB InstantiatedDB) bool {
	var myEquations []cgs.FunctionEquation
	var mySets map[cgs.Vertex]([]int)
	var myFunctions map[cgs.FunctionEdge](homs.myFunction)
	myEquations = potentialDB.underlyingGraph.functionEquations
	mySets := potentialDB.underlyingSets
	myFunctions := potentialDB.underlyingFunctions
	for _, eq := range myEquations {
		mylhs := make([]homs.myFunction, len(eq.lhs))
		domainsLHS := make([][]int, len(eq.lhs))
		for i := range domainsLHS {
			domainsLHS[i] = make([]int, 0)
		}
		for i, term := range eq.lhs {
			mylhs[i] = myFunctions[term]
			domainsLHS[i] = mySets[term.GetSource()]
		}
		myrhs := make([]homs.myFunction, len(eq.rhs))
		domainsRHS := make([][]int, len(eq.rhs))
		for i := range domainsRHS {
			domainsRHS[i] = make([]int, 0)
		}
		for i, term := range eq.rhs {
			myrhs[i] = myFunctions[term]
			domainsRHS[i] = mySets[term.GetSource()]
		}
		mylhsCombined, validLHS := homs.composeManyFunctions(mylhs, domainsLHS)
		myrhsCombined, validRHS := homs.composeManyFunctions(myrhs, domainsRHS)
		//check if equal
	}
	result := true
	return result
}

func (potentialDB *InstantiatedDB) allPossiblyPartialFunctions() map[cgs.PossiblyPartialFunctionEdge]homs.possiblyPartialFunction {
	length := len(potentialDB.underlyingFunctions) + len(potentialDB.underlyingPartialFunctions)
	toReturn := make(map[cgs.PossiblyPartialFunctionEdge]homs.possiblyPartialFunction, length)
	for k, v := range potentialDB.underlyingFunctions {
		toReturn[k] = v
	}
	for k, v := range potentialDB.underlyingPartialFunctions {
		toReturn[k] = v
	}
	return toReturn
}

// not done yet
func validatePartialFunctionEquations(potentialDB InstantiatedDB) bool {
	var myEquations []cgs.PossiblyPartialFunctionEquation
	var mySets map[cgs.Vertex]([]int)
	var myPossiblyPartialFunctions map[cgs.PossiblyPartialFunctionEdge]homs.possiblyPartialFunction
	myEquations = potentialDB.underlyingGraph.partialFunctionEquations
	mySets = potentialDB.underlyingSets
	myPossiblyPartialFunctions = potentialDB.allPossiblyPartialFunctions()
	for _, eq := range myEquations {
		mylhs := make([]homs.possiblyPartialFunction, len(eq.lhs))
		domainsLHS := make([][]int, len(eq.lhs))
		for i := range domainsLHS {
			domainsLHS[i] = make([]int, 0)
		}
		for i, term := range eq.lhs {
			mylhs[i] = myPossiblyPartialFunctions[term]
			domainsLHS[i] = mySets[term.GetSource()]
		}
		myrhs := make([]homs.possiblyPartialFunction, len(eq.rhs))
		domainsRHS := make([][]int, len(eq.rhs))
		for i := range domainsRHS {
			domainsRHS[i] = make([]int, 0)
		}
		for i, term := range eq.rhs {
			myrhs[i] = myPossiblyPartialFunctions[term]
			domainsRHS[i] = mySets[term.GetSource()]
		}
		mylhsCombined, validLHS := homs.composeManyPartials(mylhs, domainsLHS)
		myrhsCombined, validRHS := homs.composeManyPartials(myrhs, domainsRHS)
		//check if equal
	}
	result := true
	return result
}

func (potentialDB *InstantiatedDB) allPossiblyRelations() map[cgs.PossiblyRelationEdge]homs.possiblyRelation {
	length := len(potentialDB.underlyingFunctions) + len(potentialDB.underlyingPartialFunctions) + len(potentialDB.underlyingRelations)
	toReturn := make(map[cgs.PossiblyPartialFunctionEdge]homs.possiblyPartialFunction, length)
	for k, v := range potentialDB.underlyingFunctions {
		toReturn[k] = v
	}
	for k, v := range potentialDB.underlyingPartialFunctions {
		toReturn[k] = v
	}
	for k, v := range potentialDB.underlyingRelations {
		toReturn[k] = v
	}
	return toReturn
}

// not done yet
func validateRelationEquations(potentialDB InstantiatedDB) bool {
	var myEquations []cgs.PossiblyPartialFunctionEquation
	var mySets map[cgs.Vertex]([]int)
	var myPossiblyRelations map[cgs.PossiblyPartialFunctionEdge]homs.possiblyPartialFunction
	myEquations = potentialDB.underlyingGraph.partialFunctionEquations
	mySets = potentialDB.underlyingSets
	myPossiblyRelations = potentialDB.allPossiblyRelations()
	for _, eq := range myEquations {
		mylhs := make([]homs.possiblyRelation, len(eq.lhs))
		domainsLHS := make([][]int, len(eq.lhs))
		for i := range domainsLHS {
			domainsLHS[i] = make([]int, 0)
		}
		for i, term := range eq.lhs {
			mylhs[i] = myPossiblyRelations[term]
			domainsLHS[i] = mySets[term.GetSource()]
		}
		myrhs := make([]homs.possiblyRelation, len(eq.rhs))
		domainsRHS := make([][]int, len(eq.rhs))
		for i := range domainsRHS {
			domainsRHS[i] = make([]int, 0)
		}
		for i, term := range eq.rhs {
			myrhs[i] = myPossiblyRelations[term]
			domainsRHS[i] = mySets[term.GetSource()]
		}
		mylhsCombined := homs.composeManyRelations(mylhs, domainsLHS)
		myrhsCombined := homs.composeManyRelations(myrhs, domainsRHS)
		//check if equal
	}
	result := true
	return result
}

// adding a disjoint vertex to the schema and the underlyingSet is given
func (currentDB *InstantiatedDB) addVertex(newVertex string, underlyingSet []int) bool {
	result = currentDB.underlyingGraph.addVertex2(newVertex)
	if !result {
		return false
	}
	currentDB.underlyingSets[cgs.Vertex{identifier: newVertex}] = underlyingSet
	return true
}

// adding function edge
func (currentDB *InstantiatedDB) addFunctionEdge(newSource string, newTarget string, description string, content homs.myFunction) bool {
	result = currentDB.underlyingGraph.addFunctionEdge2(newSource, newTarget, description)
	if !result {
		return false
	}
	sourceSet = currentDB.underlyingSets[cgs.Vertex{identifier: newSource}]
	targetSet = currentDB.underlyingSets[cgs.Vertex{identifier: newTarget}]
	result = homs.validateFunction(sourceSet, targetSet, content)
	if !result {
		_, _, _, _ = currentDB.underlyingGraph.removeFunctionEdge(description)
		return false
	}
	thisEdge, valid = currentDB.underlyingGraph.getFunctionEdgeByName(description)
	if valid {
		currentDB.underlyingFunctions[thisEdge] = content
		return true
	}
	fmt.Printf("Should never be able to get here. Because have created an edge with the name description, so should find it.")
	return false
}

// ??????
func (currentDB *InstantiatedDB) addPartialFunctionEdge(newSource string, newTarget string, description string, content homs.myPartialFunction) bool {
	result = currentDB.underlyingGraph.addPartialFunctionEdge2(newSource, newTarget, description)
	if !result {
		return false
	}
	sourceSet = currentDB.underlyingSets[cgs.Vertex{identifier: newSource}]
	targetSet = currentDB.underlyingSets[cgs.Vertex{identifier: newTarget}]
	result = homs.validatePartialFunction(sourceSet, targetSet, content)
	if !result {
		_, _, _ = currentDB.underlyingGraph.removePartialFunctionEdge(description)
		return false
	}
	thisEdge, valid = currentDB.underlyingGraph.getDefPartialFunctionEdgeByName(description)
	if valid {
		currentDB.underlyingPartialFunctions[thisEdge] = content
		return true
	}
	fmt.Printf("Should never be able to get here. Because have created an edge with the name description, so should find it.")
	return false
}

// ???????
func (currentDB *InstantiatedDB) addRelationEdge(newSource string, newTarget string, description string, content homs.myRelation) bool {
	result = currentDB.underlyingGraph.addRelationEdge2(newSource, newTarget, description)
	if !result {
		return false
	}
	sourceSet = currentDB.underlyingSets[cgs.Vertex{identifier: newSource}]
	targetSet = currentDB.underlyingSets[cgs.Vertex{identifier: newTarget}]
	result = homs.validateRelation(sourceSet, targetSet, content)
	if !result {
		_, _ = currentDB.underlyingGraph.removeRelationEdge(description)
		return false
	}
	thisEdge, valid = currentDB.underlyingGraph.getDefRelationEdgeByName(description)
	if valid {
		currentDB.underlyingRelations[thisEdge] = content
		return true
	}
	fmt.Printf("Should never be able to get here. Because have created an edge with the name description, so should find it.")
	return false
}

// ??????????
//func addFunctionEdgeEquation(currentDB *InstantiatedDB,....){
//}

// ?????
//func addPartialFunctionEquation(currentDB *InstantiatedDB,....){
//}

// ??????
//func addRelationEquation(currentDB *InstantiatedDB,....){
//}

// ????????
//func removeFunctionEdgeEquation(currentDB *InstantiatedDB,....){
//}

// ????????
//func removePartialFunctionEquation(currentDB *InstantiatedDB,....){
//}

// ???????
//func removeRelationEquation(currentDB *InstantiatedDB,....){
//}

// ?????
//func removeFunctionEdge(currentDB *InstantiatedDB,newSource cgs.Vertex,newTarget cgs.Vertex,description string){
//}

// ??????
//func removePartialFunctionEdge(currentDB *InstantiatedDB,newSource cgs.Vertex,newTarget cgs.Vertex,description string){
//}

// ???????
//func removeRelationEdge(currentDB *InstantiatedDB,newSource cgs.Vertex,newTarget cgs.Vertex,description string){
//}

// ????
//func deleteVertex(currentDB *InstantiatedDB,badVertex cgs.Vertex){
//}

// for all the function edges that go out from modifiedVertex need to supply values on addedItem for those functions
// for all the partialfunction edges that go out from modifiedVertex either supply value or say it is undefined on this
// for all the relations edges that go out from this vertex, decide what y (addedItem,y) go into the relation
//          possibly default to []
// for all the relations edges that go into this vertex, decide what y (y,addedItem) go into the relation
//          possibly default so that relation[y] does not add addedItem into the list, so none of (y,addedItem) are in relation
//          possibly default so that relation[y] does add addedItem into the list, so all of (y,addedItem) are in relation
//func addElementToSet(currentDB *InstantiatedDB,modifiedVertex Vertex,addedItem int){}

//func deleteElementToSet(currentDB *InstatntiatedDB,modifiedVertex cgs.Vertex,deletedItem int){}

//func modifyAFunction
//func modifyAPartialFunction
//func modifyARelation
