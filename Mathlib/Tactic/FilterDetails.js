window;import{jsxs as e,jsx as n,Fragment as t}from"react/jsx-runtime";import*as r from"react";import i from"react";import{RpcContext as o,useAsyncPersistent as s,mapRpcError as c,importWidgetModule as a}from"@leanprover/infoview";function l(e,n,t,r){return new(t||(t=Promise))((function(i,o){function s(e){try{a(r.next(e))}catch(e){o(e)}}function c(e){try{a(r.throw(e))}catch(e){o(e)}}function a(e){var n;e.done?i(e.value):(n=e.value,n instanceof t?n:new t((function(e){e(n)}))).then(s,c)}a((r=r.apply(e,n||[])).next())}))}function m(i,o,s){return l(this,void 0,void 0,(function*(){if("text"in s)return n(t,{children:s.text});if("element"in s){const[e,t,c]=s.element,a={};for(const[e,n]of t)a[e]=n;const d=yield Promise.all(c.map((e=>l(this,void 0,void 0,(function*(){return yield m(i,o,e)})))));return"hr"===e?n("hr",{}):0===d.length?r.createElement(e,a):r.createElement(e,a,d)}if("component"in s){const[e,n,t,c]=s.component,d=yield Promise.all(c.map((e=>l(this,void 0,void 0,(function*(){return yield m(i,o,e)}))))),u=Object.assign(Object.assign({},t),{pos:o}),f=yield a(i,o,e);if(!(n in f))throw new Error(`Module '${e}' does not export '${n}'`);return 0===d.length?r.createElement(f[n],u):r.createElement(f[n],u,d)}return e("span",Object.assign({className:"red"},{children:["Unknown HTML variant: ",JSON.stringify(s)]}))}))}function d({pos:i,html:a}){const l=r.useContext(o),d=s((()=>m(l,i,a)),[l,i,a]);return"resolved"===d.state?d.value:"rejected"===d.state?e("span",Object.assign({className:"red"},{children:["Error rendering HTML: ",c(d.error).message]})):n(t,{})}function u(t){const[r,o]=i.useState(t.initiallyFiltered);return e("details",Object.assign({open:!0},{children:[e("summary",Object.assign({className:"mv2 pointer"},{children:[t.message,n("span",Object.assign({className:"fr",onClick:e=>{e.preventDefault()}},{children:n("a",{className:"link pointer mh2 dim codicon codicon-filter",title:"filter",onClick:e=>{o((e=>!e))}})}))]})),n(d,{pos:t.pos,html:r?t.filtered:t.all})]}))}"function"==typeof SuppressedError&&SuppressedError;export{u as default};
