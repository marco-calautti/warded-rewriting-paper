# warded-rewriter

Algorithm that rewrites a given set of Warded TGDs and a conjunctive query to an equivalent Datalog query. 

The algorithm uses a stripped down version of the [IRIS library](https://bitbucket.org/giorsi/nyaya) for rule parsing, unification, and other basic operations on rules.

## How to build

`mvn compile assembly:single`

## How to use

See the [examples](https://gitlab.com/mcalautti/warded-rewriter/-/tree/main/warded-rewriter/example-inputs) on how to format a set of TGDs together with queries to rewrite in a dtg file.

### Per-query rewriting

To rewrite each query in the dtg file individually, run:

`java -jar \<warded-rewriter jar\> <dtg file>`

The above command will produce a file for each query, corresponding to its Datalog rewriting.

### Bulk rewriting 
In a bulk scenario, the assumption is that all the queries in the dtg file must be answered all in one reasoning pass. The Warded rewriter supports this scenario, by performing a "bulk rewrite".

In this case, the queries are all rewritten in a single computation of the algorithm. This allows the algorithm to reuse computations made across the different queries, and thus, potentially speed up the whole rewriting process. A bulk rewrite is performed as follows:

`java -jar \<warded-rewriter jar\> <dtg file> --bulk`

The result is a *single* file containing all rewritten queries. Running a Datalog engine over this file will produce the output of *all* queries in one pass. The advantage is that now multiple queries can share intermediate computations, thus making the computation of all the answers potentially faster than running each rewritten query individually. 
