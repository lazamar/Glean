"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[525],{3905:function(e,n,t){t.r(n),t.d(n,{MDXContext:function(){return d},MDXProvider:function(){return h},mdx:function(){return x},useMDXComponents:function(){return c},withMDXComponents:function(){return m}});var a=t(67294);function i(e,n,t){return n in e?Object.defineProperty(e,n,{value:t,enumerable:!0,configurable:!0,writable:!0}):e[n]=t,e}function r(){return r=Object.assign||function(e){for(var n=1;n<arguments.length;n++){var t=arguments[n];for(var a in t)Object.prototype.hasOwnProperty.call(t,a)&&(e[a]=t[a])}return e},r.apply(this,arguments)}function l(e,n){var t=Object.keys(e);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);n&&(a=a.filter((function(n){return Object.getOwnPropertyDescriptor(e,n).enumerable}))),t.push.apply(t,a)}return t}function s(e){for(var n=1;n<arguments.length;n++){var t=null!=arguments[n]?arguments[n]:{};n%2?l(Object(t),!0).forEach((function(n){i(e,n,t[n])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(t)):l(Object(t)).forEach((function(n){Object.defineProperty(e,n,Object.getOwnPropertyDescriptor(t,n))}))}return e}function o(e,n){if(null==e)return{};var t,a,i=function(e,n){if(null==e)return{};var t,a,i={},r=Object.keys(e);for(a=0;a<r.length;a++)t=r[a],n.indexOf(t)>=0||(i[t]=e[t]);return i}(e,n);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);for(a=0;a<r.length;a++)t=r[a],n.indexOf(t)>=0||Object.prototype.propertyIsEnumerable.call(e,t)&&(i[t]=e[t])}return i}var d=a.createContext({}),m=function(e){return function(n){var t=c(n.components);return a.createElement(e,r({},n,{components:t}))}},c=function(e){var n=a.useContext(d),t=n;return e&&(t="function"==typeof e?e(n):s(s({},n),e)),t},h=function(e){var n=c(e.components);return a.createElement(d.Provider,{value:n},e.children)},p={inlineCode:"code",wrapper:function(e){var n=e.children;return a.createElement(a.Fragment,{},n)}},u=a.forwardRef((function(e,n){var t=e.components,i=e.mdxType,r=e.originalType,l=e.parentName,d=o(e,["components","mdxType","originalType","parentName"]),m=c(t),h=i,u=m["".concat(l,".").concat(h)]||m[h]||p[h]||r;return t?a.createElement(u,s(s({ref:n},d),{},{components:t})):a.createElement(u,s({ref:n},d))}));function x(e,n){var t=arguments,i=n&&n.mdxType;if("string"==typeof e||i){var r=t.length,l=new Array(r);l[0]=u;var s={};for(var o in n)hasOwnProperty.call(n,o)&&(s[o]=n[o]);s.originalType=e,s.mdxType="string"==typeof e?e:i,l[1]=s;for(var d=2;d<r;d++)l[d]=t[d];return a.createElement.apply(null,l)}return a.createElement.apply(null,t)}u.displayName="MDXCreateElement"},75475:function(e,n,t){t.r(n),t.d(n,{contentTitle:function(){return m},default:function(){return u},frontMatter:function(){return d},metadata:function(){return c},toc:function(){return h}});var a=t(83117),i=t(80102),r=(t(67294),t(3905)),l=t.p+"assets/images/migration-before-f6a81cf38e48e3bad614aa0164b327a6.png",s=t.p+"assets/images/migration-after-61c0e0d94c886aaae9506c4b92ae9198.png",o=["components"],d={id:"migration",title:"How do I migrate a schema?",sidebar_label:"Migrating a schema"},m="Migrating schemas",c={unversionedId:"schema/migration",id:"schema/migration",isDocsHomePage:!1,title:"How do I migrate a schema?",description:"TL;DR:",source:"@site/docs/schema/migration.md",sourceDirName:"schema",slug:"/schema/migration",permalink:"/docs/schema/migration",editUrl:"https://github.com/facebookincubator/Glean/tree/main/glean/website/docs/schema/migration.md",tags:[],version:"current",frontMatter:{id:"migration",title:"How do I migrate a schema?",sidebar_label:"Migrating a schema"},sidebar:"someSidebar",previous:{title:"Changing a schema",permalink:"/docs/schema/changing"},next:{title:"Workflow",permalink:"/docs/schema/workflow"}},h=[{value:"Guiding example",id:"guiding-example",children:[],level:2},{value:"Changing the schema files",id:"changing-the-schema-files",children:[],level:2},{value:"Deploying changes",id:"deploying-changes",children:[],level:2},{value:"Schema Dependencies",id:"schema-dependencies",children:[],level:2},{value:"Version Resolution",id:"version-resolution",children:[{value:"The <code>all</code> schema",id:"the-all-schema",children:[],level:3},{value:"Conflict resolution",id:"conflict-resolution",children:[],level:3}],level:2}],p={toc:h};function u(e){var n=e.components,t=(0,i.Z)(e,o);return(0,r.mdx)("wrapper",(0,a.Z)({},p,t,{components:n,mdxType:"MDXLayout"}),(0,r.mdx)("h1",{id:"migrating-schemas"},"Migrating schemas"),(0,r.mdx)("p",null,"TL;DR:"),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},"Make only backwards compatible changes in schema migrations."),(0,r.mdx)("li",{parentName:"ul"},"Always update the indexer and schema at the same time."),(0,r.mdx)("li",{parentName:"ul"},"Use the ",(0,r.mdx)("inlineCode",{parentName:"li"},"evolves")," feature to guarantee clients don\u2019t break during the migration.")),(0,r.mdx)("hr",null),(0,r.mdx)("p",null,"Migrating schemas in Glean doesn\u2019t need to be hard, but to ensure there will be no disruption of live services you need to consider multiple parts of the system."),(0,r.mdx)("h2",{id:"guiding-example"},"Guiding example"),(0,r.mdx)("p",null,"This guide will walk through an example migration and explain the main points to be taken into account in the process. It assumes you are familiar with the ",(0,r.mdx)("a",{parentName:"p",href:"https://www.internalfb.com/intern/staticdocs/glean/docs/schema/changing/#schema-migrations-with-backward-compatible-changes"},(0,r.mdx)("inlineCode",{parentName:"a"},"evolves")," feature.")),(0,r.mdx)("p",null,"To start suppose you use the following schema to represent classes and their methods."),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema code.1 {\n    predicate Class : { name: string }\n    predicate Method : { class : Class, name : string }\n}\nschema all.1 : code.1 {}\n")),(0,r.mdx)("p",null,"The goal will be to augment the representation to support storing whether a method is static or not."),(0,r.mdx)("p",null,"To do that you will need to add a field to the ",(0,r.mdx)("inlineCode",{parentName:"p"},"Method")," predicate. This change requires you to create a new version of the schema (see ",(0,r.mdx)("a",{parentName:"p",href:"https://www.internalfb.com/intern/staticdocs/glean/docs/schema/changing/"},"How do I change a schema"),"). You will also need a new version of the ",(0,r.mdx)("inlineCode",{parentName:"p"},"all")," schema (see ",(0,r.mdx)("strong",{parentName:"p"},(0,r.mdx)("em",{parentName:"strong"},"Version Resolution")),")."),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema code.2 {\n    predicate Class : { name: string }\n    predicate Method : { class : Class, name : string, static: bool }\n}\nschema code.2 evolves code.1\nschema all.2 : code.2 {}\n")),(0,r.mdx)("p",null,"Keep in mind that ",(0,r.mdx)("inlineCode",{parentName:"p"},"code.2 { predicate Method { class: Class, ..}}")," is just syntactic sugar for ",(0,r.mdx)("inlineCode",{parentName:"p"},"predicate code.Method.2 { class: code.Class.2, ...}")," so when we say updating a schema, what we really mean is updating all the individual predicates in a schema. Each predicate is independent"),(0,r.mdx)("h2",{id:"changing-the-schema-files"},"Changing the schema files"),(0,r.mdx)("p",null,"This ",(0,r.mdx)("inlineCode",{parentName:"p"},"code")," schema might live in some path in the project like ",(0,r.mdx)("inlineCode",{parentName:"p"},"/schema/source/code.angle"),".\nIt is worth having an archive folder such as ",(0,r.mdx)("inlineCode",{parentName:"p"},"/schema/source/archive/")," where old versions are moved to. We cannot remove an old schema version while there may still be clients using it.\nBy having an archive directory the original file can contain only the most current version of the schema and the changes between versions are shown much more clearly in version control."),(0,r.mdx)("h2",{id:"deploying-changes"},"Deploying changes"),(0,r.mdx)("p",null,"You need a plan to deploy this update. Let\u2019s start by looking at the initial state of the system."),(0,r.mdx)("img",{src:l,alt:"System diagram - before migration"}),(0,r.mdx)("p",null,"The ",(0,r.mdx)("em",{parentName:"p"},"Indexer")," generates facts and sends them to the ",(0,r.mdx)("em",{parentName:"p"},"Glean Write Server"),". The write server will use the ",(0,r.mdx)("em",{parentName:"p"},"Schemas")," to determine the shape each saved fact should have and save them to a ",(0,r.mdx)("em",{parentName:"p"},"Database"),". The ",(0,r.mdx)("em",{parentName:"p"},"Schemas")," used during the creation of the ",(0,r.mdx)("em",{parentName:"p"},"Database")," will be saved into the database itself and will determine how the Query Server should interpret client queries."),(0,r.mdx)("p",null,"In the diagram we can see that there are two types of clients:"),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},"Clients that make versioned queries, that is with predicate versions (e.g. ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method.1 _"),").",(0,r.mdx)("ul",{parentName:"li"},(0,r.mdx)("li",{parentName:"ul"},"These are usually using a DSL such as the Hack or Haskell ones and use Thrift or a binary encoding of the results. If there is any unexpected bit in the result decoding will fail."),(0,r.mdx)("li",{parentName:"ul"},"If a specific version is requested the server will only return facts with exactly the expected shape."),(0,r.mdx)("li",{parentName:"ul"},"Although one can omit predicate versions in the Haskell and Hack DSLs these libraries will still create queries with explicit version numbers. The libraries use code generation and the version numbers are determined at compilation time."))),(0,r.mdx)("li",{parentName:"ul"},"Clients that make unversioned queries, without predicate versions (e.g. ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method _"),").",(0,r.mdx)("ul",{parentName:"li"},(0,r.mdx)("li",{parentName:"ul"},"These are applications using clients without a DSL (like the Python client) or constructing their queries using strings, like in ",(0,r.mdx)("inlineCode",{parentName:"li"},"glean shell"),"."),(0,r.mdx)("li",{parentName:"ul"},"They receive results in JSON."),(0,r.mdx)("li",{parentName:"ul"},"The server will determine the version to be used based on the standard ",(0,r.mdx)("strong",{parentName:"li"},(0,r.mdx)("em",{parentName:"strong"},"Version Resolution"))," procedure.")))),(0,r.mdx)("p",null,"When you create a new schema version you also create new versions of all predicates inside that schema. If we are not careful in the process of updating the indexers and clients we could end up in a situation where clients are expecting predicates of one version and the server is operating on predicates of a different one."),(0,r.mdx)("p",null,"This could lead to two problems when deploying changes:"),(0,r.mdx)("ol",null,(0,r.mdx)("li",{parentName:"ol"},"Clients breaking with unexpected response content.",(0,r.mdx)("ol",{parentName:"li"},(0,r.mdx)("li",{parentName:"ol"},"A type changes in a backwards incompatible way in a schema migration and clients issuing unversioned queries start getting the new type with the unexpected shape."))),(0,r.mdx)("li",{parentName:"ol"},"Clients getting empty responses.",(0,r.mdx)("ol",{parentName:"li"},(0,r.mdx)("li",{parentName:"ol"},"Client requests ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method.1")," but the db only has ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method.2")," and ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.2")," doesn\u2019t evolve ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.1")),(0,r.mdx)("li",{parentName:"ol"},"Client requests ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method.2")," but the database only has ",(0,r.mdx)("inlineCode",{parentName:"li"},"code.Method.1")," facts.")))),(0,r.mdx)("p",null,"The way to avoid problem 1 is to never create backwards incompatible changes. If you need such a change it is best to create a schema with a different name and have the indexer create facts for both old and new schemas while all clients are being updated."),(0,r.mdx)("p",null,"Problem number 2 can be eliminated by deploying new schemas, indexers and clients in the following order and using the ",(0,r.mdx)("inlineCode",{parentName:"p"},"evolves")," feature to guarantee that all clients work during the transition:"),(0,r.mdx)("ol",null,(0,r.mdx)("li",{parentName:"ol"},"Stop running indexers using your schema."),(0,r.mdx)("li",{parentName:"ol"},"Publish the new schema."),(0,r.mdx)("li",{parentName:"ol"},"Deploy the updated indexer"),(0,r.mdx)("li",{parentName:"ol"},"Enable indexing using your schema again."),(0,r.mdx)("li",{parentName:"ol"},"Wait until a database with the new schema is created."),(0,r.mdx)("li",{parentName:"ol"},"Update clients.")),(0,r.mdx)("p",null,"Step 5 ensures that we don\u2019t update clients before the server is using a database capable of answering their new queries."),(0,r.mdx)("p",null,"The diagram below shows the intermediate state of the system after step 5 but before we have updated all clients. Changes are in bold. The blue text represents facts from the new schema transformed through the ",(0,r.mdx)("inlineCode",{parentName:"p"},"evolves"),"  feature into the shape of facts from the old schema to answer versioned queries from non-updated clients."),(0,r.mdx)("img",{src:s,alt:"System diagram - after migration"}),(0,r.mdx)("p",null,"Now that the server side is done clients can be updated at their leisure."),(0,r.mdx)("h2",{id:"schema-dependencies"},"Schema Dependencies"),(0,r.mdx)("p",null,"There might be many schemas that depend on ",(0,r.mdx)("inlineCode",{parentName:"p"},"code.1"),". If you need to update them to import ",(0,r.mdx)("inlineCode",{parentName:"p"},"code.2")," instead you will need to create new versions of them as well. You will need to update dependant schemas if:"),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},"A schema uses predicates/types from the old schema in a predicate/type.")),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema inheritance.1 {\n   import code.1\n   predicate Inherits : { child: code.Class, parent: code.Class }\n}\n")),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},"A schema use predicates/types from the old schema in the derivation of a stored predicate.")),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema inheritance.roots.1 {\n   import code.1\n   predicate IsRoot : Class\n        stored C where\n            C = code.Class _ ;\n            !(Inherits { child = C });\n}\n")),(0,r.mdx)("p",null,"If a dependant schema only uses types from the old schema in the derivation of non-stored predicates there is no need to create a new schema version."),(0,r.mdx)("p",null,"If you create a new version of a dependant schema you may also need to create new versions for the schemas that depend on it and so on. The criterion for whether that is needed is the same as the one above."),(0,r.mdx)("p",null,"New versions of dependant schemas should evolve the old dependant schema version and should be added to the new ",(0,r.mdx)("inlineCode",{parentName:"p"},"all")," schema."),(0,r.mdx)("p",null,"Let\u2019s now look in a bit more detail into how clients issuing unversioned queries are affected by the migration."),(0,r.mdx)("h2",{id:"version-resolution"},"Version Resolution"),(0,r.mdx)("p",null,"To answer queries without explicit versions the server must determine a version to be used for each predicate and type in the query."),(0,r.mdx)("p",null,"Each predicate has a version, which is derived from the name of its schema."),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema src.1 {\n    predicate File : string\n}\n")),(0,r.mdx)("p",null,"The schema above defines the predicate ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.File.1"),"."),(0,r.mdx)("p",null,"When a query is sent to a Glean server it may or may not include the version of the predicate it wants."),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},(0,r.mdx)("inlineCode",{parentName:"li"},"src.File.1 _")," - Query to fetch all facts from this exact predicate."),(0,r.mdx)("li",{parentName:"ul"},(0,r.mdx)("inlineCode",{parentName:"li"},"src.File _")," - Omit predicate version number and let the server determine what version should be used.")),(0,r.mdx)("h3",{id:"the-all-schema"},"The ",(0,r.mdx)("inlineCode",{parentName:"h3"},"all")," schema"),(0,r.mdx)("p",null,"To determine what predicate to return when the server receives an unversioned query Glean uses a special schema named ",(0,r.mdx)("inlineCode",{parentName:"p"},"all"),"."),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema all.1 : src.1 {}\n")),(0,r.mdx)("p",null,"The statement above means that with ",(0,r.mdx)("inlineCode",{parentName:"p"},"all.1")," any unversioned predicate with the ",(0,r.mdx)("inlineCode",{parentName:"p"},"src")," qualification should be interpreted as being part of the ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.1")," schema. That is, the query ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.File _")," should be interpreted as ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.File.1 _"),"."),(0,r.mdx)("p",null,"When there are multiple versions of the ",(0,r.mdx)("inlineCode",{parentName:"p"},"all")," schema available, the Glean server will apply these rules (in this order) to establish which one should be used:"),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},"The version specified in the ",(0,r.mdx)("inlineCode",{parentName:"li"},"schema_version")," field of the query request. By default clients don\u2019t specify this field."),(0,r.mdx)("li",{parentName:"ul"},"The latest version of ",(0,r.mdx)("inlineCode",{parentName:"li"},"all")," at the time the database was created. This is stored in the database property ",(0,r.mdx)("inlineCode",{parentName:"li"},"glean.schema_version"),", which can be seen with the command ",(0,r.mdx)("inlineCode",{parentName:"li"},":describe")," in the shell.")),(0,r.mdx)("p",null,"Here is a full example. Suppose we create a database using a schema file with the following content:"),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema src.1 {\n    predicate File : string\n}\nschema src.2 {\n    predicate File : { name : string, executable : bool }\n}\nschema all.1 : src.1 {}\nschema all.2 : src.2 {}\n")),(0,r.mdx)("p",null,"The database will use ",(0,r.mdx)("inlineCode",{parentName:"p"},"all.2")," as its schema for version resolution and this is the outcome of the following queries:"),(0,r.mdx)("ul",null,(0,r.mdx)("li",{parentName:"ul"},(0,r.mdx)("inlineCode",{parentName:"li"},"src.File _")," - Will yield results of type ",(0,r.mdx)("inlineCode",{parentName:"li"},"src.File.2"),"."),(0,r.mdx)("li",{parentName:"ul"},(0,r.mdx)("inlineCode",{parentName:"li"},"src.File.2 _")," - Will yield results of type ",(0,r.mdx)("inlineCode",{parentName:"li"},"src.File.2"),"."),(0,r.mdx)("li",{parentName:"ul"},(0,r.mdx)("inlineCode",{parentName:"li"},'src.File "/tools"..')," - Error. Because it resolves to ",(0,r.mdx)("inlineCode",{parentName:"li"},"src.File.2")," this is a type mismatch as the predicate content is a record and not a string.")),(0,r.mdx)("h3",{id:"conflict-resolution"},"Conflict resolution"),(0,r.mdx)("p",null,"If we had"),(0,r.mdx)("pre",null,(0,r.mdx)("code",{parentName:"pre"},"schema all.2 : src.1, src.2 {}\n")),(0,r.mdx)("p",null,"What would ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.File _")," resolve to? When multiple versions are available in the ",(0,r.mdx)("inlineCode",{parentName:"p"},"all")," schema, the type or predicate with the highest version number is selected. In this case ",(0,r.mdx)("inlineCode",{parentName:"p"},"src.File.2"),"."))}u.isMDXComponent=!0}}]);