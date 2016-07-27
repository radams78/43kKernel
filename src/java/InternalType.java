public enum InternalType { 
    none(0, false, false), 
    isolated(1, false, false),
    top(1, true, false), 
    bottom(1, false, true), 
    universal(1, true, true), 
    bothTopAndBottom(2, true, true);
    
    public final int numVertices;
    public final boolean hasTopVertex;
    public final boolean hasBottomVertex;
    
    InternalType(int numVertices, boolean hasTopVertex, boolean hasBottomVertex) {
	this.numVertices = numVertices;
	this.hasTopVertex = hasTopVertex;
	this.hasBottomVertex = hasBottomVertex;
    }
}
