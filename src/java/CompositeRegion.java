import java.io.*;

public class CompositeRegion extends Region {
    Signature sig;
    
    private CompositeRegionDescriptor desc;
    private Region topRegion;
    private BasicRegion bottomRegion;
    private boolean signatureIsComputed;
    
    public RegionDescriptor getDescriptor() {return desc;}
    
    CompositeRegion(BoundaryGarden g, Region topRegion, BasicRegion bottomRegion) {
	super(g, g.getGluingResult(topRegion.boundaryID, bottomRegion.boundaryID), 
	      topRegion.size + bottomRegion.size - (g.getBoundary(topRegion.boundaryID).bottomPathLength() + 2), "", ""); // TODO Force value here
	
	desc = new CompositeRegionDescriptor(topRegion.getDescriptor(), (BasicRegionDescriptor) bottomRegion.getDescriptor());
	signatureIsComputed = false;
	this.topRegion = topRegion;
	this.bottomRegion = bottomRegion;
    }
    
    private void computeSignature() {
	SignatureComputer sigCom = myGarden.getSignatureComputer(topRegion.boundaryID, bottomRegion.boundaryID);		
	sig = sigCom.outerSignature(topRegion.getSignature(), bottomRegion.getSignature());
	signatureIsComputed = true;
    }
    
    public Signature getSignature() {
	if(!signatureIsComputed) computeSignature();
	return sig;	
    }
}
