package coloredGraphSchema

import "fmt"

type Vertex struct {
	identifier string
}

func (v Vertex) GetIdentifier() string {
	return v.identifier
}

type UnspecifiedEdge interface {
	GetSource() Vertex
	GetTarget() Vertex
	GetIdentifier() string
	Contains(string) bool
}

type PossiblyRelationEdge interface {
	UnspecifiedEdge
	Junk2() string
}

type PossiblyPartialFunctionEdge interface {
	PossiblyRelationEdge
	Junk1() string
}

type FunctionEdge struct {
	source     Vertex
	target     Vertex
	identifier string
}

func (f FunctionEdge) GetSource() Vertex {
	return f.source
}

func (f FunctionEdge) GetTarget() Vertex {
	return f.target
}

func (f FunctionEdge) GetIdentifier() string {
	return f.identifier
}

func (f FunctionEdge) Junk1() string {
	return "A function gives a partial function"
}

func (f FunctionEdge) Junk2() string {
	return "A function gives a relation"
}

func (f FunctionEdge) Contains(badVertexName string) bool {
	return f.GetSource().identifier == badVertexName || f.GetTarget().identifier == badVertexName
}

type PartialFunctionEdge struct {
	source     Vertex
	target     Vertex
	identifier string
}

func (f PartialFunctionEdge) Junk1() string {
	return "A partial function gives a partial function"
}

func (f PartialFunctionEdge) Junk2() string {
	return "A partial function gives a relation"
}

func (f PartialFunctionEdge) GetSource() Vertex {
	return f.source
}

func (f PartialFunctionEdge) GetTarget() Vertex {
	return f.target
}

func (f PartialFunctionEdge) GetIdentifier() string {
	return f.identifier
}

func (f PartialFunctionEdge) Contains(badVertexName string) bool {
	return f.GetSource().identifier == badVertexName || f.GetTarget().identifier == badVertexName
}

type RelationEdge struct {
	source     Vertex
	target     Vertex
	identifier string
}

func (f RelationEdge) Junk2() string {
	return "A relation gives a relation"
}

func (f RelationEdge) GetSource() Vertex {
	return f.source
}

func (f RelationEdge) GetTarget() Vertex {
	return f.target
}

func (f RelationEdge) GetIdentifier() string {
	return f.identifier
}

func (f RelationEdge) Contains(badVertexName string) bool {
	return f.GetSource().identifier == badVertexName || f.GetTarget().identifier == badVertexName
}

// check all in each path composable in order
// since already have it, returns the target of the path
// at the very end
// second argument is only meaningful if the first is true
func validPath(path1 []PossiblyRelationEdge) (bool, Vertex) {
	var currentVertex Vertex
	toReturn := true
	for i, edge := range path1 {
		if i != 0 {
			toReturn = (edge.GetSource() == currentVertex)
		}
		if !toReturn {
			return false, currentVertex
		}
		currentVertex = edge.GetTarget()
	}
	return toReturn, currentVertex
}

//two paths given in the graph which will become two morphisms in Rel upon the instantiation functor
//check to make sure they are valid paths in the graph and that they share source and target
//so path1,path2 \in Hom(common source,common target) and makes sense to ask for them to be equal
//when path1=[] and path2 !=[], assume path1 stands for identity arrow at source of path2
// so path2 must be a loop coming back to that source
// same for vice versa
//[]=[] is defaulted to true but meaningless to impose it
func imposableRelationEquation(path1, path2 []PossiblyRelationEdge) bool {
	result := true
	switch {
	case len(path1) > 0 && len(path2) > 0:
		result = (path1[0].GetSource() == path2[0].GetSource())
		result2, target1 := validPath(path1)
		result3, target2 := validPath(path2)
		return result && result2 && result3 && (target1 == target2)
	case len(path2) > 0:
		// path1 is empty so path2 should form a loop so can impose that it is identity on that vertex
		result2, target2 := validPath(path2)
		result = result2 && (target2 == path2[0].GetSource())
	case len(path1) > 0:
		// path2 is empty so path1 should form a loop so can impose that it is identity on that vertex
		result1, target1 := validPath(path1)
		result = result1 && (target1 == path1[0].GetSource())
	}
	return true
}

type GeneralEquation interface {
	GetLHS() []PossiblyRelationEdge
	GetRHS() []PossiblyRelationEdge
	GetIdentifier() string
	Contains(edgeName string) bool
}

type FunctionEquation struct {
	lhs        []FunctionEdge
	rhs        []FunctionEdge
	identifier string
}

func convertFEqToREq(lhs []FunctionEdge) []PossiblyRelationEdge {
	var interfaceSlice []PossiblyRelationEdge = make([]PossiblyRelationEdge, len(lhs))
	for i, d := range lhs {
		interfaceSlice[i] = d
	}
	return interfaceSlice
}

func (feq FunctionEquation) GetIdentifier() string {
	return feq.identifier
}

func (feq FunctionEquation) GetLHS() []PossiblyRelationEdge {
	return convertFEqToREq(feq.lhs)
}

func (feq FunctionEquation) GetRHS() []PossiblyRelationEdge {
	return convertFEqToREq(feq.rhs)
}

func (feq FunctionEquation) Contains(edgeName string) bool {
	for _, currentEdge := range feq.lhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	for _, currentEdge := range feq.rhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	return false
}

type PossiblyPartialFunctionEquation struct {
	lhs        []PossiblyPartialFunctionEdge
	rhs        []PossiblyPartialFunctionEdge
	identifier string
}

func convertPFEqToREq(lhs []PossiblyPartialFunctionEdge) []PossiblyRelationEdge {
	var interfaceSlice []PossiblyRelationEdge = make([]PossiblyRelationEdge, len(lhs))
	for i, d := range lhs {
		interfaceSlice[i] = d
	}
	return interfaceSlice
}

func (feq PossiblyPartialFunctionEquation) GetIdentifier() string {
	return feq.identifier
}

func (feq PossiblyPartialFunctionEquation) GetLHS() []PossiblyRelationEdge {
	return convertPFEqToREq(feq.lhs)
}

func (feq PossiblyPartialFunctionEquation) GetRHS() []PossiblyRelationEdge {
	return convertPFEqToREq(feq.rhs)
}

func (feq PossiblyPartialFunctionEquation) Contains(edgeName string) bool {
	for _, currentEdge := range feq.lhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	for _, currentEdge := range feq.rhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	return false
}

type PossiblyRelationEquation struct {
	lhs        []PossiblyRelationEdge
	rhs        []PossiblyRelationEdge
	identifier string
}

func (feq PossiblyRelationEquation) GetIdentifier() string {
	return feq.identifier
}

func (feq PossiblyRelationEquation) GetLHS() []PossiblyRelationEdge {
	return feq.lhs
}

func (feq PossiblyRelationEquation) GetRHS() []PossiblyRelationEdge {
	return feq.rhs
}

func (feq PossiblyRelationEquation) Contains(edgeName string) bool {
	for _, currentEdge := range feq.lhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	for _, currentEdge := range feq.rhs {
		if currentEdge.GetIdentifier() == edgeName {
			return true
		}
	}
	return false
}

type SchemaGraph struct {
	vertices                 []Vertex
	functionEdges            []FunctionEdge
	partialFunctionEdges     []PartialFunctionEdge
	relationEdges            []RelationEdge
	functionEquations        []FunctionEquation
	partialFunctionEquations []PossiblyPartialFunctionEquation
	relationEquations        []PossiblyRelationEquation
}

func (potentialSchema *SchemaGraph) displayInfo() {
	for _, v := range potentialSchema.vertices {
		fmt.Println("Vertex: " + v.GetIdentifier())
	}
	for _, fe := range potentialSchema.functionEdges {
		fmt.Println("FunctionEdge: " + fe.GetIdentifier())
	}
	for _, pfe := range potentialSchema.partialFunctionEdges {
		fmt.Println("PartialFunctionEdge: " + pfe.GetIdentifier())
	}
	for _, re := range potentialSchema.relationEdges {
		fmt.Println("RelationEdge: " + re.GetIdentifier())
	}
	for _, fe := range potentialSchema.functionEquations {
		fmt.Println("FunctionEquation: " + fe.GetIdentifier())
	}
	for _, pfe := range potentialSchema.partialFunctionEquations {
		fmt.Println("PossiblyPartialFunctionEquation: " + pfe.GetIdentifier())
	}
	for _, re := range potentialSchema.relationEquations {
		fmt.Println("PossiblyRelationEquation: " + re.GetIdentifier())
	}

}

func (potentialSchema *SchemaGraph) presentVertices() map[Vertex]bool {
	myVertexMap := make(map[Vertex]bool)
	for _, vertex := range potentialSchema.vertices {
		myVertexMap[vertex] = true
	}
	return myVertexMap
}

func presentVertices2(myVertices []Vertex) map[Vertex]bool {
	myVertexMap := make(map[Vertex]bool)
	for _, vertex := range myVertices {
		myVertexMap[vertex] = true
	}
	return myVertexMap
}

func vertexInVertices(a Vertex, list []Vertex) bool {
	for _, b := range list {
		if b == a {
			return true
		}
	}
	return false
}

func vertexInVertices2(a string, list []Vertex) bool {
	return vertexInVertices(Vertex{identifier: a}, list)
}

func presentEdgesF(myEdges []FunctionEdge) map[PossiblyRelationEdge]bool {
	myEdgeMap := make(map[PossiblyRelationEdge]bool)
	for _, edge := range myEdges {
		myEdgeMap[edge] = true
	}
	return myEdgeMap
}

func presentEdgesPF(myEdges []PartialFunctionEdge) map[PossiblyRelationEdge]bool {
	myEdgeMap := make(map[PossiblyRelationEdge]bool)
	for _, edge := range myEdges {
		myEdgeMap[edge] = true
	}
	return myEdgeMap
}

func presentEdgesR(myEdges []RelationEdge) map[PossiblyRelationEdge]bool {
	myEdgeMap := make(map[PossiblyRelationEdge]bool)
	for _, edge := range myEdges {
		myEdgeMap[edge] = true
	}
	return myEdgeMap
}

func addPresentEdgesF(alreadyKnown map[PossiblyRelationEdge]bool, myEdges []FunctionEdge) map[PossiblyRelationEdge]bool {
	for _, edge := range myEdges {
		alreadyKnown[edge] = true
	}
	return alreadyKnown
}

func addPresentEdgesPF(alreadyKnown map[PossiblyRelationEdge]bool, myEdges []PartialFunctionEdge) map[PossiblyRelationEdge]bool {
	for _, edge := range myEdges {
		alreadyKnown[edge] = true
	}
	return alreadyKnown
}

func addPresentEdgesR(alreadyKnown map[PossiblyRelationEdge]bool, myEdges []RelationEdge) map[PossiblyRelationEdge]bool {
	for _, edge := range myEdges {
		alreadyKnown[edge] = true
	}
	return alreadyKnown
}

func validateImposableEquation(equationToImpose GeneralEquation, allValidEdges map[PossiblyRelationEdge]bool) bool {
	var lhs, rhs []PossiblyRelationEdge
	result := true
	lhs = equationToImpose.GetLHS()
	for _, currentEdge := range lhs {
		result = result && allValidEdges[currentEdge]
		if !result {
			return false
		}
	}
	rhs = equationToImpose.GetRHS()
	for _, currentEdge := range rhs {
		result = result && allValidEdges[currentEdge]
		if !result {
			return false
		}
	}
	result = imposableRelationEquation(lhs, rhs)
	return result
}

func validateImposableEquationsF(equationsToImpose []FunctionEquation, allValidEdges map[PossiblyRelationEdge]bool) bool {
	result := true
	for _, currentEquation := range equationsToImpose {
		result = validateImposableEquation(currentEquation, allValidEdges)
		if !result {
			return false
		}
	}
	return result
}

func validateImposableEquationsPF(equationsToImpose []PossiblyPartialFunctionEquation, allValidEdges map[PossiblyRelationEdge]bool) bool {
	result := true
	for _, currentEquation := range equationsToImpose {
		result = validateImposableEquation(currentEquation, allValidEdges)
		if !result {
			return false
		}
	}
	return result
}

func validateImposableEquationsR(equationsToImpose []PossiblyRelationEquation, allValidEdges map[PossiblyRelationEdge]bool) bool {
	result := true
	for _, currentEquation := range equationsToImpose {
		result = validateImposableEquation(currentEquation, allValidEdges)
		if !result {
			return false
		}
	}
	return result
}

func validateGraph(potentialSchema SchemaGraph) bool {
	myFunctionEdges := potentialSchema.functionEdges
	myPartialFunctionEdges := potentialSchema.partialFunctionEdges
	myRelationEdges := potentialSchema.relationEdges
	result := true
	myVertexMap := potentialSchema.presentVertices()
	for _, edge := range myFunctionEdges {
		sourceVertex := edge.source
		targetVertex := edge.target
		result = myVertexMap[sourceVertex] && myVertexMap[targetVertex]
		if !result {
			return false
		}
	}
	for _, edge := range myPartialFunctionEdges {
		sourceVertex := edge.source
		targetVertex := edge.target
		result = myVertexMap[sourceVertex] && myVertexMap[targetVertex]
		if !result {
			return false
		}
	}
	for _, edge := range myRelationEdges {
		sourceVertex := edge.source
		targetVertex := edge.target
		result = myVertexMap[sourceVertex] && myVertexMap[targetVertex]
		if !result {
			return false
		}
	}
	// imposable function equations
	myPresentEdges := presentEdgesF(myFunctionEdges)
	result = validateImposableEquationsF(potentialSchema.functionEquations, myPresentEdges)
	if !result {
		return false
	}
	// imposable partial function equations
	myPresentEdges = addPresentEdgesPF(myPresentEdges, myPartialFunctionEdges)
	result = validateImposableEquationsPF(potentialSchema.partialFunctionEquations, myPresentEdges)
	if !result {
		return false
	}
	// imposable relation equations
	myPresentEdges = addPresentEdgesR(myPresentEdges, myRelationEdges)
	result = validateImposableEquationsR(potentialSchema.relationEquations, myPresentEdges)
	return result
}

func emptySchemaGraph() SchemaGraph {
	returnVal1 := make([]Vertex, 0)
	returnVal2 := make([]FunctionEdge, 0)
	returnVal3 := make([]PartialFunctionEdge, 0)
	returnVal4 := make([]RelationEdge, 0)
	returnVal5 := make([]FunctionEquation, 0)
	returnVal6 := make([]PossiblyPartialFunctionEquation, 0)
	returnVal7 := make([]PossiblyRelationEquation, 0)
	return SchemaGraph{vertices: returnVal1, functionEdges: returnVal2, partialFunctionEdges: returnVal3, relationEdges: returnVal4, functionEquations: returnVal5, partialFunctionEquations: returnVal6, relationEquations: returnVal7}
}

// nothing can go wrong with validation
// just a disjoint extra vertex
// might be a repeated name which will cause problems later
func (startingSchema *SchemaGraph) addVertex2(newVertex string) bool {
	if vertexInVertices2(newVertex, startingSchema.vertices) {
		return false
	}
	startingSchema.vertices = append(startingSchema.vertices, Vertex{identifier: newVertex})
	return true
}

func (startingSchema *SchemaGraph) addVertex(newVertex Vertex) bool {
	if vertexInVertices(newVertex, startingSchema.vertices) {
		return false
	}
	startingSchema.vertices = append(startingSchema.vertices, newVertex)
	return true
}

//make sure both source and target of this prospective edge are in the graph
// does not check if this edge is already there
func (startingSchema *SchemaGraph) addFunctionEdge(newSource Vertex, newTarget Vertex, description string) bool {
	sourceOK := vertexInVertices(newSource, startingSchema.vertices)
	targetOK := vertexInVertices(newTarget, startingSchema.vertices)
	if sourceOK && targetOK {
		newEdge := FunctionEdge{source: newSource, target: newTarget, identifier: description}
		startingSchema.functionEdges = append(startingSchema.functionEdges, newEdge)
		return true
	}
	return false
}

// does not check if this edge is already there
func (startingSchema *SchemaGraph) addFunctionEdge2(newSource string, newTarget string, description string) bool {
	newSource2 := Vertex{identifier: newSource}
	newTarget2 := Vertex{identifier: newTarget}
	return startingSchema.addFunctionEdge(newSource2, newTarget2, description)
}

func (startingSchema *SchemaGraph) addCartesianProductVertex(factor1, factor2 Vertex) bool {
	factor1OK := vertexInVertices(factor1, startingSchema.vertices)
	factor2OK := vertexInVertices(factor2, startingSchema.vertices)
	if factor1OK && factor2OK {
		name := factor1.GetIdentifier() + " X " + factor2.GetIdentifier()
		startingSchema.addVertex2(name)
		startingSchema.addFunctionEdge2(name, factor1.GetIdentifier(), name+" projection 1")
		startingSchema.addFunctionEdge2(name, factor2.GetIdentifier(), name+" projection 2")
		return true
	}
	return false
}

//make sure both source and target of this prospective edge are in the graph
// does not check if this edge is already there
func (startingSchema *SchemaGraph) addPartialFunctionEdge(newSource Vertex, newTarget Vertex, description string) bool {
	sourceOK := vertexInVertices(newSource, startingSchema.vertices)
	targetOK := vertexInVertices(newTarget, startingSchema.vertices)
	if sourceOK && targetOK {
		newEdge := PartialFunctionEdge{source: newSource, target: newTarget, identifier: description}
		startingSchema.partialFunctionEdges = append(startingSchema.partialFunctionEdges, newEdge)
		return true
	}
	return false
}

// does not check if this edge is already there
func (startingSchema *SchemaGraph) addPartialFunctionEdge2(newSource string, newTarget string, description string) bool {
	newSource2 := Vertex{identifier: newSource}
	newTarget2 := Vertex{identifier: newTarget}
	return startingSchema.addPartialFunctionEdge(newSource2, newTarget2, description)
}

//make sure both source and target of this prospective edge are in the graph
// does not check if this edge is already there
func (startingSchema *SchemaGraph) addRelationEdge(newSource Vertex, newTarget Vertex, description string) bool {
	sourceOK := vertexInVertices(newSource, startingSchema.vertices)
	targetOK := vertexInVertices(newTarget, startingSchema.vertices)
	if sourceOK && targetOK {
		newEdge := RelationEdge{source: newSource, target: newTarget, identifier: description}
		startingSchema.relationEdges = append(startingSchema.relationEdges, newEdge)
		return true
	}
	return false
}

// does not check if this edge is already there
func (startingSchema *SchemaGraph) addRelationEdge2(newSource string, newTarget string, description string) bool {
	newSource2 := Vertex{identifier: newSource}
	newTarget2 := Vertex{identifier: newTarget}
	return startingSchema.addRelationEdge(newSource2, newTarget2, description)
}

//all the edges in both lhs and rhs must be in the graph already
//they must both be valid paths
//they must share source and target
// does not check if this equation is already there
func (startingSchema *SchemaGraph) addFunctionEquation(equation FunctionEquation) bool {
	imposableEquation := validateImposableEquation(equation, presentEdgesF(startingSchema.functionEdges))
	if imposableEquation {
		startingSchema.functionEquations = append(startingSchema.functionEquations, equation)
		return true
	}
	return false
}

func dummyVertex() Vertex {
	return Vertex{identifier: "This is a dummy Vertex"}
}

func dummyEdge() FunctionEdge {
	return FunctionEdge{source: dummyVertex(), target: dummyVertex(), identifier: "This is a dummy edge"}
}

func (startingSchema *SchemaGraph) getFunctionEdgeByName(name string) (FunctionEdge, bool) {
	for _, currentEdge := range startingSchema.functionEdges {
		if currentEdge.GetIdentifier() == name {
			return currentEdge, true
		}
	}
	return dummyEdge(), false
}

func (startingSchema *SchemaGraph) getPartialFunctionEdgeByName(name string) (PossiblyPartialFunctionEdge, bool) {
	toReturn, success := startingSchema.getFunctionEdgeByName(name)
	if success {
		return toReturn, true
	}
	for _, currentEdge := range startingSchema.partialFunctionEdges {
		if currentEdge.GetIdentifier() == name {
			return currentEdge, true
		}
	}
	return dummyEdge(), false
}

func (startingSchema *SchemaGraph) getRelationEdgeByName(name string) (PossiblyRelationEdge, bool) {
	toReturn, success := startingSchema.getPartialFunctionEdgeByName(name)
	if success {
		return toReturn, true
	}
	for _, currentEdge := range startingSchema.relationEdges {
		if currentEdge.GetIdentifier() == name {
			return currentEdge, true
		}
	}
	return dummyEdge(), false
}

// does not check if this equation is already there
func (startingSchema *SchemaGraph) addFunctionEquation2(lhsToBe []string, rhsToBe []string, identifierToBe string) bool {
	newlhs := make([]FunctionEdge, len(lhsToBe))
	newrhs := make([]FunctionEdge, len(rhsToBe))
	var success bool
	for i, currentString := range lhsToBe {
		newlhs[i], success = startingSchema.getFunctionEdgeByName(currentString)
		if !success {
			return false
		}
	}
	for i, currentString := range rhsToBe {
		newrhs[i], success = startingSchema.getFunctionEdgeByName(currentString)
		if !success {
			return false
		}
	}
	return startingSchema.addFunctionEquation(FunctionEquation{lhs: newlhs, rhs: newrhs, identifier: identifierToBe})
}

//all the edges in both lhs and rhs must be in the graph already
//they must both be valid paths
//they must share source and target
// does not check if this equation is already there
func (startingSchema *SchemaGraph) addPartialFunctionEquation(equation PossiblyPartialFunctionEquation) bool {
	myPresentEdges := presentEdgesF(startingSchema.functionEdges)
	myPresentEdges = addPresentEdgesPF(myPresentEdges, startingSchema.partialFunctionEdges)
	imposableEquation := validateImposableEquation(equation, myPresentEdges)
	if imposableEquation {
		startingSchema.partialFunctionEquations = append(startingSchema.partialFunctionEquations, equation)
		return true
	}
	return false
}

// does not check if this equation is already there
func (startingSchema *SchemaGraph) addPartialFunctionEquation2(lhsToBe []string, rhsToBe []string, identifierToBe string) bool {
	newlhs := make([]PossiblyPartialFunctionEdge, len(lhsToBe))
	newrhs := make([]PossiblyPartialFunctionEdge, len(rhsToBe))
	var success bool
	for i, currentString := range lhsToBe {
		newlhs[i], success = startingSchema.getPartialFunctionEdgeByName(currentString)
		if !success {
			return false
		}
	}
	for i, currentString := range rhsToBe {
		newrhs[i], success = startingSchema.getPartialFunctionEdgeByName(currentString)
		if !success {
			return false
		}
	}
	return startingSchema.addPartialFunctionEquation(PossiblyPartialFunctionEquation{lhs: newlhs, rhs: newrhs, identifier: identifierToBe})
}

//all the edges in both lhs and rhs must be in the graph already
//they must both be valid paths
//they must share source and target
// does not check if this equation is already there
func (startingSchema *SchemaGraph) addRelationEquation(equation PossiblyRelationEquation) bool {
	myPresentEdges := presentEdgesF(startingSchema.functionEdges)
	myPresentEdges = addPresentEdgesPF(myPresentEdges, startingSchema.partialFunctionEdges)
	myPresentEdges = addPresentEdgesR(myPresentEdges, startingSchema.relationEdges)
	imposableEquation := validateImposableEquation(equation, myPresentEdges)
	if imposableEquation {
		startingSchema.relationEquations = append(startingSchema.relationEquations, equation)
		return true
	}
	return false
}

// does not check if this equation is already there
func (startingSchema *SchemaGraph) addRelationEquation2(lhsToBe []string, rhsToBe []string, identifierToBe string) bool {
	newlhs := make([]PossiblyRelationEdge, len(lhsToBe))
	newrhs := make([]PossiblyRelationEdge, len(rhsToBe))
	var success bool
	for i, currentString := range lhsToBe {
		newlhs[i], success = startingSchema.getRelationEdgeByName(currentString)
		if !success {
			return false
		}
	}
	for i, currentString := range rhsToBe {
		newrhs[i], success = startingSchema.getRelationEdgeByName(currentString)
		if !success {
			return false
		}
	}
	return startingSchema.addRelationEquation(PossiblyRelationEquation{lhs: newlhs, rhs: newrhs, identifier: identifierToBe})
}

// nothing goes wrong with validation
func (startingSchema *SchemaGraph) removeFunctionEquation(toRemove string) int {
	indexRemove := make([]int, 0)
	for i, eq := range startingSchema.functionEquations {
		if eq.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.functionEquations = append(startingSchema.functionEquations[:i], startingSchema.functionEquations[i+1:]...)
	}
	return len(indexRemove)
}

// nothing goes wrong with validation
func (startingSchema *SchemaGraph) removePartialFunctionEquation(toRemove string) int {
	indexRemove := make([]int, 0)
	for i, eq := range startingSchema.partialFunctionEquations {
		if eq.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.partialFunctionEquations = append(startingSchema.partialFunctionEquations[:i], startingSchema.partialFunctionEquations[i+1:]...)
	}
	return len(indexRemove)
}

// nothing goes wrong with validation
func (startingSchema *SchemaGraph) removeRelationEquation(toRemove string) int {
	indexRemove := make([]int, 0)
	for i, eq := range startingSchema.relationEquations {
		if eq.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.relationEquations = append(startingSchema.relationEquations[:i], startingSchema.relationEquations[i+1:]...)
	}
	return len(indexRemove)
}

// when an edge gets removed all the equations that use it get removed as well
func (startingSchema *SchemaGraph) removeFunctionEdge(toRemove string) (int, int, int, int) {
	functionEquationsToRemove := make([]string, 0)
	partialfunctionEquationsToRemove := make([]string, 0)
	relationEquationsToRemove := make([]string, 0)
	functionEquationsRemoved := 0
	partialFunctionEquationsRemoved := 0
	relationEquationsRemoved := 0
	for _, eq := range startingSchema.functionEquations {
		if eq.Contains(toRemove) {
			functionEquationsToRemove = append(functionEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range functionEquationsToRemove {
		functionEquationsRemoved = functionEquationsRemoved + startingSchema.removeFunctionEquation(eqName)
	}
	for _, eq := range startingSchema.partialFunctionEquations {
		if eq.Contains(toRemove) {
			partialfunctionEquationsToRemove = append(partialfunctionEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range partialfunctionEquationsToRemove {
		partialFunctionEquationsRemoved = partialFunctionEquationsRemoved + startingSchema.removePartialFunctionEquation(eqName)
	}
	for _, eq := range startingSchema.relationEquations {
		if eq.Contains(toRemove) {
			relationEquationsToRemove = append(relationEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range relationEquationsToRemove {
		relationEquationsRemoved = relationEquationsRemoved + startingSchema.removeRelationEquation(eqName)
	}
	indexRemove := make([]int, 0)
	for i, currentEdge := range startingSchema.functionEdges {
		if currentEdge.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.functionEdges = append(startingSchema.functionEdges[:i], startingSchema.functionEdges[i+1:]...)
	}
	return functionEquationsRemoved, partialFunctionEquationsRemoved, relationEquationsRemoved, len(indexRemove)
}

func (startingSchema *SchemaGraph) removePartialFunctionEdge(toRemove string) (int, int, int) {
	partialfunctionEquationsToRemove := make([]string, 0)
	relationEquationsToRemove := make([]string, 0)
	partialFunctionEquationsRemoved := 0
	relationEquationsRemoved := 0
	for _, eq := range startingSchema.partialFunctionEquations {
		if eq.Contains(toRemove) {
			partialfunctionEquationsToRemove = append(partialfunctionEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range partialfunctionEquationsToRemove {
		partialFunctionEquationsRemoved = partialFunctionEquationsRemoved + startingSchema.removePartialFunctionEquation(eqName)
	}
	for _, eq := range startingSchema.relationEquations {
		if eq.Contains(toRemove) {
			relationEquationsToRemove = append(relationEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range relationEquationsToRemove {
		relationEquationsRemoved = relationEquationsRemoved + startingSchema.removeRelationEquation(eqName)
	}
	indexRemove := make([]int, 0)
	for i, currentEdge := range startingSchema.partialFunctionEdges {
		if currentEdge.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.partialFunctionEdges = append(startingSchema.partialFunctionEdges[:i], startingSchema.partialFunctionEdges[i+1:]...)
	}
	return partialFunctionEquationsRemoved, relationEquationsRemoved, len(indexRemove)
}

func (startingSchema *SchemaGraph) removeRelationEdge(toRemove string) (int, int) {
	relationEquationsToRemove := make([]string, 0)
	relationEquationsRemoved := 0
	for _, eq := range startingSchema.relationEquations {
		if eq.Contains(toRemove) {
			relationEquationsToRemove = append(relationEquationsToRemove, eq.GetIdentifier())
		}
	}
	for _, eqName := range relationEquationsToRemove {
		relationEquationsRemoved = relationEquationsRemoved + startingSchema.removeRelationEquation(eqName)
	}
	indexRemove := make([]int, 0)
	for i, currentEdge := range startingSchema.partialFunctionEdges {
		if currentEdge.GetIdentifier() == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.partialFunctionEdges = append(startingSchema.partialFunctionEdges[:i], startingSchema.partialFunctionEdges[i+1:]...)
	}
	return relationEquationsRemoved, len(indexRemove)
}

//every edge incident on this must be removed
func (startingSchema *SchemaGraph) deleteVertex(toRemove string) (int, int, int, int, int, int, int) {
	functionEdgesRemoved := 0
	partialFunctionEdgesRemoved := 0
	relationEdgesRemoved := 0
	functionEqsRemoved := 0
	partialFunctionEqsRemoved := 0
	relationEqsRemoved := 0
	for _, currentEdge := range startingSchema.functionEdges {
		if currentEdge.Contains(toRemove) {
			a, b, c, d := startingSchema.removeFunctionEdge(currentEdge.GetIdentifier())
			functionEqsRemoved = functionEqsRemoved + a
			partialFunctionEqsRemoved = partialFunctionEqsRemoved + b
			relationEqsRemoved = relationEqsRemoved + c
			functionEdgesRemoved = functionEdgesRemoved + d
		}
	}
	for _, currentEdge := range startingSchema.partialFunctionEdges {
		if currentEdge.Contains(toRemove) {
			b, c, d := startingSchema.removePartialFunctionEdge(currentEdge.GetIdentifier())
			partialFunctionEqsRemoved = partialFunctionEqsRemoved + b
			relationEqsRemoved = relationEqsRemoved + c
			partialFunctionEdgesRemoved = partialFunctionEdgesRemoved + d
		}
	}
	for _, currentEdge := range startingSchema.relationEdges {
		if currentEdge.Contains(toRemove) {
			c, d := startingSchema.removeRelationEdge(currentEdge.GetIdentifier())
			relationEqsRemoved = relationEqsRemoved + c
			relationEdgesRemoved = relationEdgesRemoved + d
		}
	}
	indexRemove := make([]int, 0)
	for i, currentVertex := range startingSchema.vertices {
		if currentVertex.identifier == toRemove {
			indexRemove = append(indexRemove, i)
		}
	}
	for _, i := range indexRemove {
		startingSchema.vertices = append(startingSchema.vertices[:i], startingSchema.vertices[i+1:]...)
	}
	return functionEqsRemoved, partialFunctionEqsRemoved, relationEqsRemoved, functionEdgesRemoved, partialFunctionEdgesRemoved, relationEdgesRemoved, len(indexRemove)
}

func testCase() {
	var exampleGraph SchemaGraph = emptySchemaGraph()
	//exampleGraph.addVertex(Vertex{identifier: "Employee"})
	//exampleGraph.addVertex(Vertex{identifier: "Department"})
	//exampleGraph.addVertex(Vertex{identifier: "PeopleNames"})
	//exampleGraph.addVertex(Vertex{identifier: "DeptNames"})
	exampleGraph.addVertex2("Employee")
	exampleGraph.addVertex2("Department")
	exampleGraph.addVertex2("PeopleNames")
	exampleGraph.addVertex2("DeptNames")
	//exampleGraph.addFunctionEdge(Vertex{identifier: "Employee"}, Vertex{identifier: "Employee"}, "manager")
	//exampleGraph.addPartialFunctionEdge(Vertex{identifier: "Employee"}, Vertex{identifier: "Department"}, "worksIn")
	//exampleGraph.addFunctionEdge(Vertex{identifier: "Department"}, Vertex{identifier: "Employee"}, "secretary")
	//exampleGraph.addFunctionEdge(Vertex{identifier: "Department"}, Vertex{identifier: "DeptNames"}, "dept name")
	//exampleGraph.addFunctionEdge(Vertex{identifier: "Employee"}, Vertex{identifier: "PeopleNames"}, "first name")
	//exampleGraph.addFunctionEdge(Vertex{identifier: "Employee"}, Vertex{identifier: "PeopleNames"}, "last name")
	exampleGraph.addFunctionEdge2("Employee", "Employee", "manager")
	exampleGraph.addPartialFunctionEdge2("Employee", "Department", "worksIn")
	exampleGraph.addFunctionEdge2("Department", "Employee", "secretary")
	exampleGraph.addFunctionEdge2("Department", "DeptNames", "dept name")
	exampleGraph.addFunctionEdge2("Employee", "PeopleNames", "first name")
	exampleGraph.addFunctionEdge2("Employee", "PeopleNames", "last name")
	lhsToBe := []string{"secretary", "worksIn"}
	rhsToBe := []string{}
	exampleGraph.addPartialFunctionEquation2(lhsToBe, rhsToBe, "secretaries work in the correct department")
	exampleGraph.displayInfo()
}
