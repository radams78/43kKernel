import java.io.*;
import java.util.*;

// Generates all basic regions with a particular boundary.
public class BasicRegionGenerator {

    BoundaryGarden myGarden;
    int boundaryId;
    Boundary myBoundary;
    String name;
    
    boolean topPathIsLong,  bottomPathIsLong, leftSideHasRoom, rightSideHasRoom, canHaveLeftEdge, canHaveRightEdge;
    
    List<BasicRegion> basicRegions;
    List<BasicRegion> getAllBasicRegions() {return basicRegions;}
    
    BasicRegionGenerator(BoundaryGarden g, int boundaryId) {
	this.myGarden = g;
	this.boundaryId = boundaryId;
	this.myBoundary = myGarden.getBoundary(boundaryId);
	
	this.topPathIsLong = (myBoundary.topPathLength() == 2);
	this.bottomPathIsLong = (myBoundary.bottomPathLength() == 2);
	this.leftSideHasRoom =  (myBoundary.topPathVertex(1) != myBoundary.bottomPathVertex(1));
	this.rightSideHasRoom = (myBoundary.topPathVertex(myBoundary.topPathLength()) != myBoundary.bottomPathVertex(myBoundary.bottomPathLength()));
	
	this.canHaveLeftEdge = 		topPathIsLong && bottomPathIsLong 
	    && !myBoundary.areNeighbors(myBoundary.topPathVertex(1), myBoundary.bottomPathVertex(1));
	
	this.canHaveRightEdge = 		topPathIsLong && bottomPathIsLong 
	    && !myBoundary.areNeighbors(myBoundary.topPathVertex(2), myBoundary.bottomPathVertex(2));

	setAllBasicRegions();
    }
    
    private void setAllBasicRegions() {
	ArrayList<BasicRegion> ans = new ArrayList<BasicRegion>();
	int counter = 0;
	
	boolean[] truthValues = {true, false};
	
	for(InternalType leftInternalType : InternalType.values()) { 
	    for(boolean hasLeftEdge : truthValues) {
		if(!verifyTypeAndEdge(leftInternalType, hasLeftEdge, leftSideHasRoom, canHaveLeftEdge)) continue;
		
		for(InternalType rightInternalType : InternalType.values()) {
		    for(boolean hasRightEdge : truthValues) {
			if(!verifyTypeAndEdge(rightInternalType, hasRightEdge, rightSideHasRoom, canHaveRightEdge)) continue;
			
			ans.add(new BasicRegion(myGarden, boundaryId, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge));
			counter++;
			
		    }
		}
	    }
	}
	
	basicRegions = ans;
    }
    
    private boolean verifyTypeAndEdge(InternalType internalType, boolean hasEdge, boolean sideHasRoom, boolean canHaveEdge) {
	// no room --> type = none AND no leftvedge.
	if(!sideHasRoom && (internalType != InternalType.none || hasEdge)) return false;
	
	// if has edge --> can have that edge.
	if(hasEdge && !canHaveEdge) return false;
	
	// if has top vertex --> top path is long
	if(internalType.hasTopVertex && !topPathIsLong) return false;
	
	// if has bottom vertex --> bottom path is long
	if(internalType.hasBottomVertex && !bottomPathIsLong) return false;
	
	return true;
    }

    /*
     * @pre Coq: requires definition of myGarden.getBoundary(boundaryID) earlier in proof script
     */
    public CoqObject toCoq() {
	return CoqObject.coqList(basicRegions, BasicRegion.COQTYPE); //TODO Duplication with coqListInteger
    }
}
