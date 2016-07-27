import java.util.*;
import java.io.*;

public class BasicRegion extends Region {
    final static String COQTYPE = "BasicRegion";
    final static String CONSTRUCTOR = "mkBasicRegion";
    
    private List<Pair<Vertex, Vertex> > internalEdges;
    
    public final InternalType leftInternalType, rightInternalType;
    
    private Signature mySignature;
    public Signature getSignature() {return mySignature;}
    
    private BasicRegionDescriptor desc;
    public RegionDescriptor getDescriptor() {return desc;}
    
    private static int computeSize(BoundaryGarden g, int boundaryID, InternalType leftInternalType, InternalType rightInternalType) {
	return g.getBoundary(boundaryID).size + leftInternalType.numVertices + rightInternalType.numVertices; 
    }
    
    BasicRegion(BoundaryGarden g, int boundaryID, InternalType leftInternalType, InternalType rightInternalType, boolean hasLeftEdge, boolean hasRightEdge) {
	super(g, boundaryID, computeSize(g, boundaryID, leftInternalType, rightInternalType), COQTYPE, CONSTRUCTOR + " (" + g.getBoundary(boundaryID).getValue() + ") " + leftInternalType + " " + rightInternalType + " " + hasLeftEdge + " " + hasRightEdge); // TODO Duplication with g.getBoundary(boundaryID)?
	this.leftInternalType = leftInternalType;
	this.rightInternalType = rightInternalType;
	
	// Set the descriptor
	this.desc = new BasicRegionDescriptor(g, boundaryID, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge);
	
	internalEdges = new LinkedList<Pair<Vertex, Vertex> > ();
	if(hasLeftEdge) {
	    internalEdges.add(new Pair<Vertex, Vertex> (myBoundary.topPathVertex(1), myBoundary.bottomPathVertex(1)));			
	}
	
	if(hasRightEdge) {
	    internalEdges.add(new Pair<Vertex, Vertex> (myBoundary.topPathVertex(2), myBoundary.bottomPathVertex(2)));			
	}
	
	
	setSignature();
    }
    
    public void setSignature() {
	ArrayList<Integer> sig = new ArrayList<Integer> ();
	for(InputPair inp : myGarden.getAllInputs(boundaryID)) {
	    sig.add(computeSignatureAt(inp.first, inp.second));
	}
	mySignature = new Signature(sig);
    }
    
    private int computeSignatureAt(Set<Vertex> X, Set<Vertex> D) {
	if(dominatesAll(X,D)) return 0;
	
	for(Vertex v : myBoundary.vertexSet()) {
	    Set<Vertex> bigX = new TreeSet<Vertex> (X);
	    bigX.add(v);
	    if(dominatesAll(bigX, D)) return 1;
	}
	return 2;
    }
    
    private boolean dominatesAll(Set<Vertex> X, Set<Vertex> D) {
	return dominatesBoundary(X,D) && dominatesInternal(X);
    }
    
    private boolean dominatesBoundary(Set<Vertex> X, Set<Vertex> D) {
	Set<Vertex> NX =  myBoundary.neighbors(X);
	for(Pair<Vertex, Vertex> edge : internalEdges) {
	    if(X.contains(edge.first)) NX.add(edge.second);
	    if(X.contains(edge.second)) NX.add(edge.first);
	}
	return NX.containsAll(D);
    }
    
    private boolean dominatesInternal(Set<Vertex> X) {return dominatesLeftInternal(X) && dominatesRightInternal(X);}
    
    private boolean dominatesLeftInternal(Set<Vertex> X) {
	if(X.contains(myBoundary.topPathVertex(0))) return true;
	
	switch(leftInternalType) {
	case none: return true;
	case isolated: return false;
	case top: return X.contains(myBoundary.topPathVertex(1));
	case bottom: return X.contains(myBoundary.bottomPathVertex(1));
	case universal: return X.contains(myBoundary.topPathVertex(1)) || X.contains(myBoundary.bottomPathVertex(1));
	case bothTopAndBottom: return X.contains(myBoundary.topPathVertex(1)) && X.contains(myBoundary.bottomPathVertex(1));
	default: return false;
	}
	
    }
    
    private boolean dominatesRightInternal(Set<Vertex> X) {
	if(X.contains(myBoundary.topPathVertex(myBoundary.topPathLength() + 1))) return true;
	
	switch(rightInternalType) {
	case none: return true;
	case isolated: return false;
	case top: return X.contains(myBoundary.topPathVertex(2));
	case bottom: return X.contains(myBoundary.bottomPathVertex(2));
	case universal: return X.contains(myBoundary.topPathVertex(2)) || X.contains(myBoundary.bottomPathVertex(2));
	case bothTopAndBottom: return X.contains(myBoundary.topPathVertex(2)) && X.contains(myBoundary.bottomPathVertex(2));
	default: return false;
	}
    }
    
    public boolean equals(Object o) {
	if(!(o instanceof BasicRegion)) return false;
	BasicRegion br = (BasicRegion) o;
	return getDescriptor().equals(br.getDescriptor());
    }
}
