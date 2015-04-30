open util/integer
open lib/graphInheritance
open lib/basicProperties

pred isSpanningTree(g, tree : UGraph) {
	not (g = tree)
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
    connected[tree]
}

pred isInterestingSpanningTree(g, tree : UGraph) {
	isSpanningTree[g, tree]
	not undirectedAcyclic[g]
	all disj g1, g2: Graph |
		g1.edges != g2.edges
}

pred isMST(g, tree : UGraph) {
    isSpanningTree[g, tree]
    no tree2 : UGraph {
        isSpanningTree[g, tree2]
        lt[(sum edge : tree.edges | edge.weight), 
           (sum edge : tree2.edges | edge.weight)]
	}
}

run isInterestingSpanningTree for exactly 3 Vertex, exactly 8 Graph, 3 Edge, 1 Univ
