open util/integer
open lib/graphInheritance
open lib/basicProperties

fun sumOfWeights(g : Graph) : Int {
	sum edge : g.edges | edge.weight
}

pred smallWeights {
	all e : Edge |
		e.weight < 10 and e.weight > -10
}

pred allGraphsExist {
	all es : set Edge |
		some g : Graph |
			g.edges = es
}

pred isSpanningTree(g, tree : UGraph) {
	not (g = tree)
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
    connected[tree]
}

pred isInterestingSpanningTree(g, tree : UGraph) {
	smallWeights
	isSpanningTree[g, tree]
	not undirectedAcyclic[g]
	all disj g1, g2: UGraph |
		g1.edges != g2.edges
	all edgesSubset : set g.edges |
		some otherGraph: UGraph {
			otherGraph.edges = edgesSubset
		}
	all disj e1, e2 : Edge |
		e1.weight != e2.weight
}

pred isMST(g, tree : UGraph) {
	isInterestingSpanningTree[g, tree]
	no tree2 : UGraph {
        	isInterestingSpanningTree[g, tree2]
        	gt[sumOfWeights[tree], 
              sumOfWeights[tree2]]
	}
}


pred smallerT (es : set Edge, num : Int) {
	
}

pred edgesMST (g, tree : UGraph) {
	smallWeights
	g.edges != tree.edges
	isSpanningTree[g, tree]
}

--run isMST for exactly 3 Vertex, exactly 8 Graph, 3 Edge, 1 Univ

--run edgesMST for 10 Int

run isInterestingSpanningTree
