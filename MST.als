open util/integer
open lib/graph
open lib/properties

pred isSpanningTree(tree, graph: UGraph) {
	graph.vertices = tree.vertices
	tree.edges in graph.edges
	undirectedAcyclic[tree.edges, tree.vertices]
	connected[tree.edges, tree.vertices]     
}

pred isInterestingSpanningTree(tree, graph: UGraph) {
	isSpanningTree[tree, graph]
	complete[graph.edges, Vertex]
	smallWeights
}

fact noDuplicates {
	all disj g1, g2: Graph |
		g1.edges != g2.edges
	all disj e1, e2: Edge |
		e1.weight != e2.weight
}

pred isMST(tree, graph: UGraph) {
	isInterestingSpanningTree[tree, graph]
	no edgeSubset: set graph.edges {
		#edgeSubset = sub[#graph.vertices, 1]
        	connected[edgeSubset, graph.vertices]
        	gt[sumOfWeights[tree.edges], sumOfWeights[edgeSubset]]
	}
}

fun sumOfWeights(es: set Edge) : Int {
	sum edge : es | edge.weight
}

pred smallWeights {
	all e : Edge |
		e.weight < 10 and e.weight > -10
}

assert alwaysSomeMST {
	
}

//run isMST for exactly 4 Vertex,  2 Graph, 6 Edge, 10 Int
