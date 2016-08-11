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

    //TODO Duplication
    public CoqObject toCoq(Path.PathLength topPathLength, Path.PathLength bottomPathLength) {
	switch(this) {
	case none: return new CoqObject("InternalType", "none " + topPathLength + " " + bottomPathLength);
	case isolated: return new CoqObject("InternalType", "isolated " + topPathLength + " " + bottomPathLength);
	case top: return new CoqObject("InternalType", "top " + bottomPathLength);
	case bottom: return new CoqObject("InternalType", "bottom " + topPathLength);
	case universal: return new CoqObject("InternalType", "universal");
	case bothTopAndBottom: return new CoqObject("InternalType", "bothTopAndBottom");
	default: throw new AssertionError("InternalType not recognised");
	}
    }
}
