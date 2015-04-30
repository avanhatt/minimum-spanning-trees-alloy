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
}

pred isMST(g, tree : UGraph) {
    isSpanningTree[g, tree]
    no tree2 : UGraph {
        isSpanningTree[g, tree2]
        gt[sum edge : tree.edges | edge.weight, 
           sum edge : tree2.edges | edge.weight]
	}
}

run isInterestingSpanningTree
