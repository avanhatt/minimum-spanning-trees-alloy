open util/integer
open lib/graph
open lib/properties

//determines if a set of edges form a spanning tree of a graph
pred isSpanningTree(es: set Edge, graph: UGraph) {
	graph.vertices = (graph.vertices).(es.rels) // the edges are over the same set of vertices
	es in graph.edges // the edges must be a subset of the graph's edges
	undirectedAcyclic[es, graph.vertices]
	connected[es, graph.vertices]     
}

//determines if a set of edges forms a spanning tree of a complete graph
// includes because it made the instances non-trivial (where input graph was already minimally connected
pred isInterestingSpanningTree(es: set Edge, graph: UGraph) {
	isSpanningTree[es, graph]
	complete[graph.edges, Vertex]
}

//fact that no two graphs have exactly the same edge set
fact noDuplicates {
	all disj g1, g2: Graph |
		g1.edges != g2.edges
}

//determines if a set of edges forms a minimum spanning tree of a graph
pred isMST(es: set Edge, graph: UGraph) {
	isInterestingSpanningTree[es, graph] // the edges are a spanning tree and the graph is complete
	no edgeSubset: set graph.edges {
		//there is no subset of the graph's edges that are connected and have a smaller sum than the edgeset
		#edgeSubset = sub[#graph.vertices, 1]
        	connected[edgeSubset, graph.vertices]
        	gt[sumOfWeights[es], sumOfWeights[edgeSubset]]
	}
}

//function that takes in a set of edges and returns the sum of its weights
fun sumOfWeights(es: set Edge) : Int {
	sum edge : es | edge.weight
}

//fact that all weights are positive integers less than ten
// included to avoid integer overflow when summing weights in a set
fact smallWeights {
	all e : Edge |
		e.weight < 11 and e.weight > 0
}

//assertion that every connected graph has an MST
assert alwaysSomeMST {
	some g: Graph | some es: set Edge |
		complete[g.edges, Vertex] implies isMST[es, g]
}
//no counter example found for 3, 4, and 5 vertices

run isSpanningTree for 5 Vertex,  1 Graph, 10 Edge, 10 Int

check alwaysSomeMST  for 5 Vertex,  1 Graph, 10 Edge, 10 Int

run isMST for 5 Vertex,  1 Graph, 10 Edge, 10 Int
