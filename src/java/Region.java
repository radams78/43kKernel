import java.io.*;

public abstract class Region implements CoqObject {

    protected BoundaryGarden myGarden;
    protected Boundary myBoundary;
    
    public final int boundaryID;
    public final int size;

    private String name;
    
    Region(BoundaryGarden g, int ID, int s, String name) {
	myGarden = g;
	boundaryID = ID;
	size = s;
	myBoundary = myGarden.getBoundary(boundaryID);
	this.name = name;
    }
    
    public abstract Signature getSignature(); 
	
    public abstract RegionDescriptor getDescriptor();
    
    public String toString() {return getDescriptor().toString();}
    
    public SignatureTranscript getSignatureTranscript() {
	return new SignatureTranscript(myBoundary, getSignature());
    }
    
    public String getName() { return name; }

    public String getType() { return "Region"; }
}
