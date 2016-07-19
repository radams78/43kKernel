public class CoqInteger implements CoqObject {
    private Integer value;
    public CoqInteger(Integer n) { this.value = n; }
    public Integer toInt() { return value; }
    public String getName() { return value.toString(); }
    public String getType() { return "nat"; }
    public String toCoq() { return ""; }
}
