import java.io.*;
import java.util.*;

// Generates all basic regions with a particular boundary.
public class BasicRegionGenerator {

    BoundaryGarden myGarden;
    int boundaryId;
    Boundary myBoundary;
    
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
	List<BasicRegion> ans = new ArrayList<BasicRegion> ();
	
	boolean[] truthValues = {true, false};
	
	for(int leftInternalType : BasicRegion.internalTypes) {
	    for(boolean hasLeftEdge : truthValues) {
		if(!verifyTypeAndEdge(leftInternalType, hasLeftEdge, leftSideHasRoom, canHaveLeftEdge)) continue;
		
		for(int rightInternalType : BasicRegion.internalTypes) {
		    for(boolean hasRightEdge : truthValues) {
			if(!verifyTypeAndEdge(rightInternalType, hasRightEdge, rightSideHasRoom, canHaveRightEdge)) continue;
			
			ans.add(new BasicRegion(myGarden, boundaryId, leftInternalType, rightInternalType, hasLeftEdge, hasRightEdge));
			
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
    
    void toCoq(String name, PrintWriter writer) {
	for (int i = 0; i < basicRegions.size(); i++) {
	    basicRegions.get(i).toCoq(name + "_region" + i , writer);
	    writer.println();
	}
	writer.println("Definition " + name + " : List BasicRegion :=");
	for (int i = 0; i < basicRegions.size(); i++) {
	    writer.println("  " + name + "_region" + i + " ;");
	}
	writer.println("].");
    }
}
