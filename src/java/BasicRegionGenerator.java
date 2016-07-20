import java.io.*;
import java.util.*;

// Generates all basic regions with a particular boundary.
public class BasicRegionGenerator implements CoqObject {

    BoundaryGarden myGarden;
    int boundaryId;
    Boundary myBoundary;
    String name;
    
    boolean topPathIsLong,  bottomPathIsLong, leftSideHasRoom, rightSideHasRoom, canHaveLeftEdge, canHaveRightEdge;
    
    CoqList<BasicRegion> basicRegions;
    List<BasicRegion> getAllBasicRegions() {return basicRegions;}
    
    BasicRegionGenerator(BoundaryGarden g, int boundaryId, String name) {
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
	
	this.name = name;

	setAllBasicRegions();
    }
    
    private void setAllBasicRegions() {
	CoqList<BasicRegion> ans = new CoqList<BasicRegion> (name, "BasicRegion");
	int counter = 0;
	
	boolean[] truthValues = {true, false};
	
	for(int leftInternalType : BasicRegion.internalTypes) {
	    for(boolean hasLeftEdge : truthValues) {
		if(!verifyTypeAndEdge(leftInternalType, hasLeftEdge, leftSideHasRoom, canHaveLeftEdge)) continue;
		
		for(int rightInternalType : BasicRegion.internalTypes) {
		    for(boolean hasRightEdge : truthValues) {
			if(!verifyTypeAndEdge(rightInternalType, hasRightEdge, rightSideHasRoom, canHaveRightEdge)) continue;
			
			ans.add(new BasicRegion(myGarden, boundaryId, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge, name + "_br" + counter));
			counter++;
			
		    }
		}
	    }
	}
	
	basicRegions = ans;
    }
    
    private boolean verifyTypeAndEdge(int internalType, boolean hasEdge, boolean sideHasRoom, boolean canHaveEdge) {
	// no room --> type = none AND no leftvedge.
	if(!sideHasRoom && (internalType != BasicRegion.none || hasEdge)) return false;
	
	// if has edge --> can have that edge.
	if(hasEdge && !canHaveEdge) return false;
	
	// if has top vertex --> top path is long
	if(BasicRegion.hasTopVertex.contains(internalType) && !topPathIsLong) return false;
	
	// if has bottom vertex --> bottom path is long
	if(BasicRegion.hasBottomVertex.contains(internalType) && !bottomPathIsLong) return false;
	
	return true;
    }

    /*
     * @pre Coq: requires definition of myGarden.getBoundary(boundaryID) earlier in proof script
     */
    public String toCoq() {
	return basicRegions.toCoq();
    }

    public String getName() {
	return name;
    }

    public String getType() {
	return "list Region";
    }
}
