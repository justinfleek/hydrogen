# The Web Is Forking in the Age of Agents

**Source:** YouTube Transcript (cleaned)
**Relevance:** COMPASS integration — agentic web infrastructure, agent commerce primitives, content delivery evolution

---

## Key Topics for COMPASS Integration

- **The Agentic Web Fork** — The web is splitting into two parallel layers: the human web (HTML, fonts, layouts, scroll animations) and the agent web (APIs, structured data, markdown content, payment protocols, execution environments). Same physical infrastructure, fundamentally different clients. This is the mobile web analogy all over again — the companies that build for the new client early will dominate.

- **Agent Payment Infrastructure** — Every major payment company (Coinbase, Stripe, Google, PayPal, Visa) independently converged on building agent payment rails within the same few-month window. Agents that can't spend money are fundamentally limited. This creates a new category: agents as economic entities that can earn, spend, and accumulate capital independently of their creators. COMPASS needs to understand this commerce layer.

- **Cloudflare's Markdown-for-Agents** — Cloudflare (serving ~20% of the web) now treats agents as first-class citizens by auto-converting HTML to markdown on-the-fly when an AI system requests a page. Includes token count headers for context window management. This eliminates the need for scraping/conversion middleware like Firecrawl. COMPASS content delivery strategy should account for this dual-serving model.

- **Agent-Native Search Engines** — Google's architecture is wrong-shaped for machine search. Companies like Exa.ai built search from scratch for agents — their own index, neural retrieval, embedding infrastructure. Returns raw URLs and structured data, not SERPs. 95% on SimpleQA benchmark. Latency is the real differentiator in agent workflows (669ms vs 13.6s compounds fast in multi-step chains).

- **OpenAI Skills, Shell Tools & Compaction** — Skills are versioned, mountable instruction packages (more like Docker images than chat templates). Shell tool gives agents real Linux environments. Compaction auto-summarizes context windows for long-running workflows. This is software engineering applied to AI operations — version control, testing, rollback for autonomous agents.

- **Emergent Agent Workflows / Creator Economy Disruption** — Agents chaining capabilities across unrelated services to produce outputs that previously required multiple humans and tools. Example: agent takes Amazon product link → crawls page → extracts assets → generates UGC-style product video via Kling 2.0. Content types following repeatable patterns (product descriptions, social posts, email campaigns, comparison articles) are most vulnerable.

- **Agent Security Model** — Every serious security approach treats the agent as a potential adversary, not a trusted employee. IronClaw sandboxes every tool into isolated WASM environments. OpenAI uses container isolation with org-level network allow lists. Coinbase uses enclave isolation for private keys. Every primitive that makes agents more capable also makes them more dangerous.

- **The Trust Gap** — Infrastructure being built assumes a fully autonomous 0-100 world. Humans consistently want ~70% control over agent-delegated tasks (the 70/30 rule). The gap between infrastructure capabilities and human trust willingness is the central tension of the next few years. Security incidents push the trust timeline back even as adoption grows.

---

## Clean Transcript

The most interesting thing about OpenClaw is not the agent, it's the web. The web is forking in the age of agents, and nobody's talking about it enough.

Last Tuesday, three things happened within hours of each other. Coinbase launched Agentic Wallets, which are crypto wallets designed not for people, but for agents. Cloudflare shipped Markdown for agents, a feature that automatically converts any website into agent readable markdown when an AI system requests it. And then OpenAI published a developer blog post about skills and shell tools that let agents install software dependencies, run scripts, and write files inside hosted containers. None of these companies coordinated their announcements. They didn't need to. They're all building toward the same future. They all see the Open Claw phenomenon, and that future is arriving faster than any of them or most of us expected.

In the last few videos, I've covered Open Claw's chaotic launch, the emergent behaviors that made researchers rethink agent capability and what thousands of community-built skills reveal about what people actually want from their AI agents. This video is about something bigger than Open Claw. It's about the infrastructure layer that's forming under it and underneath every agent that comes after it. It's about a new kind of web. Every major infrastructure company on the internet is now simultaneously building a different piece of what amounts to an entirely new way for commerce and interaction to get done across the internet. And those pieces are snapping together faster than most of our mental models can track.

### Every Infrastructure Company Is Building the Same Future

Let's start with the money. Agents can't do much on the web if they can't pay for things. Coinbase's Agentic Wallet solved this on the crypto side using a protocol called X402 that's already processed over 50 million machine-to-machine transactions. Yes, you heard that right, 50 million. The wallets come with programmable spending limits, session caps, and gasless trading on Coinbase's base network. Developers can spin one up in under 2 minutes with a command line tool. And the wallets use non-custodial architecture, which means that even if the agent is compromised, the keys themselves sit in secure hardware that the agent cannot access. So the agent can't leak those keys. Within 24 hours of this launch, new AI agents registered wallets on Ethereum. That's not developer experimentation. That's an ecosystem of agents with wallets forming in real time.

The use cases that Coinbase highlighted tell you where Coinbase thinks this is going. Agents that autonomously rebalance DeFi portfolios, agents that pay for API calls as they make them. Agents that purchase compute on demand and participate in creator economies. Brian Armstrong's pitch is quote, "The next generation of agents won't just advise, they'll act." Which, like, duh, that's what Open Claw is all about. But this is clearly where he's going. What he did not say is that the architecture implies that agents with wallets will become real economic entities, that can earn, that can spend, and that accumulate capital independently of the humans who created them. That's a category of software that has never existed before. And that is a whole mess of legal problems that we have not encountered yet.

### Agents as Economic Entities With Wallets

Stripe is solving the same problem on the traditional payment side. Their Agent Commerce suite, which was launched in December, allows businesses to connect a product catalog and start selling through AI agents with a single integration. They built a new payment primitive called shared payment tokens, scoped, time constrained credentials that let an agent initiate a purchase using a buyer's saved payment method without ever seeing the card number.

Stripe's fraud detection system, Radar, had to be retrained from scratch because the old signals were all calibrated for human shopping behavior. Think about what that means. Decades of fraud detection machine learning built on patterns like mouse movement variability, browsing time, session behavior, device fingerprinting, all of it became useless when the buyer is software. Agent traffic doesn't move a mouse. It doesn't browse. It doesn't exhibit the behavioral variability that distinguishes a legitimate shopper from a bot. Stripe had to build an entirely new fraud model for a client that is by any prior definition a bot. And yet now bots are purchasers. Brands including Urban, Etsy, Coach, Kate Spade, and Revolve are all already onboarding.

Google is getting in on the action, too. They launched their agent payments protocol back in September. PayPal and OpenAI partnered on instant checkout in ChatGPT. Visa built a trusted agent protocol at NRF 2026 which is a conference for this in January. Google announced the universal commerce protocol which is an open standard for agent to commerce interaction and Stripe's ACS immediately auto supports it meaning merchants who integrated Stripe's agent tools are already compatible with Google's agent shopping infrastructure without writing one more line of code. The industry consensus, as a Decrypt analyst put it, is quote, "Agents that can't spend money are fundamentally limited," which is true, but there's a whole lot down the road once you do that. Nevertheless, every major payment company reached this conclusion independently within the same couple of month window.

### Cloudflare Makes Agents First-Class Citizens

But we're not done when we're talking about payments. Let's go over to content access. The web is made of HTML, and HTML is designed for human browsers, not language models. Pages are bloated with scripts, tracking pixels, navigation menus, and ads. When an agent needs to read a web page, it has to strip all of that stuff that we humans like out of the way and convert it into something useful. Usually, that's markdown. This is such a common step that an entire category of companies like Firecrawl or Exa exists just to do that conversion.

Now, Cloudflare's Markdown for Agents cuts out that middleman. When an AI agent requests a page for any Cloudflare enabled site, it sends an accept header and Cloudflare intercepts the request, fetches the HTML from the origin server, converts it to markdown on the fly, and serves it back. The response even includes an X-Markdown-Tokens header with the estimated token count, so the agent can manage its own context window. No scraping anymore, no conversion libraries, no wasted compute. The agent just asks for markdown and gets markdown.

This matters a lot more than it might sound. Cloudflare serves roughly 20% of the web. When they decide agents are first class citizens of the web, which is what they just did. When they decide agents are not to be blocked, but rather clients who should be served in their preferred format, markdown, Cloudflare is making an infrastructure level commitment to a world where software reads websites as routinely as humans do.

And Cloudflare isn't stopping at markdown conversion. They launched three companion features in the same release. First, llms.txt and llms-full.txt, which are standardized machine readable site maps that tell agents what's on a site and how to navigate it. Just like robots.txt told search engine crawlers the exact same thing two decades ago. Second, Cloudflare launched AI Index. It's an opt-in search index where sites can make their content discoverable to agents directly through Cloudflare's MCP server and search API. And that means they can bypass Google entirely. Third and most telling, Cloudflare is including built-in X402 monetization support. So site owners can charge agents for content access using the exact same protocol as Coinbase's wallets. Cloudflare isn't just making the web readable for agents. They're building an economic layer for a web where agents pay to access content.

### Search Engines Built for Machines, Not Humans

Then there's search. Google search is optimized for humans, obviously. 10 blue links, ads, featured snippets, knowledge panels. Recently, they added AI summaries. None of that is useful to an agent that needs to programmatically find specific information and then come back with structured data. Exa.ai built a search engine from scratch specifically for agents, their own index, their own neural retrieval models, their own embedding infrastructure. Their API returns raw URLs and content, not search engine result pages. Their research endpoint chains multiple searches together, agentically parallelizing across output fields to minimize latency. It scores 95% on SimpleQA, a benchmark for factual accuracy. For comparison, Perplexity scores lower.

So, if you're thinking, is this going to be a new bar for accurate agentic search? You would be right. But the benchmark results are much less interesting than what this is all implying about the future of internet market structures. Google built a search engine for humans and spent decades perfecting it. Now there's a parallel need — search for machines — and Google's architecture is the wrong shape for that. The companies that build agent native search from first principles have an actual structural advantage, not just a marketing one.

An independent benchmark from AI Multiple tested the major agent search providers head-to-head. If Search led on a composite agent score, Firecrawl, Exa, and Parallel Pro were statistically tied behind it. But the latency spread tells you where the real differentiation is starting to live. In an agent workflow, Brave returned results in 669 milliseconds, which is about 2/3 of a second. Parallel Pro took 13.6 whole seconds. In an agent workflow where each search is one step in a long chain, that latency difference compounds into minutes really, really fast. The providers that own their own infrastructure and their own agentic index rather than wrapping Google's API have a structural speed advantage that grows much more valuable as agent workflows get more complex. And guess what? They're going to in 2026.

### OpenAI Skills, Shell Tools, and Compaction

And then there's execution. OpenAI's blog post on skills, shell, and compaction reads like a road map for turning agents into advisors and workers. Skills are reusable versioned instruction bundles. We've heard about them from Claude before. Think of them as standard operating procedures for AI for a particular task. An agent can load them on demand, immediately learn the skill, and get going. The shell tool gives agents a real terminal environment where they can install dependencies, run scripts, and write output files. Compaction manages the context window automatically so that long-running agent workflows don't crash when they hit token limits.

The details matter here because they reveal OpenAI's bet about what agent architecture actually is going to look like in production. Skills aren't prompts. They're versioned. They're mountable instruction packages. They look more like Docker images than chat templates. An organization can build a Salesforce skill, test it, lock down the version, and deploy it across every agent in the company with a guarantee that every agent follows the same procedure. When the procedure changes, you just update that skill version and every single agent will follow. You don't have to mess with system prompts or anything else. That's the difference between artisanal prompt engineering and actual software engineering applied to AI operations.

The shell tool is equally telling. It gives agents a real Linux environment, not a sandbox playground, but a terminal where they can write files to disk and type commands like install, curl, and grep. The pattern OpenAI describes — installing dependencies, fetching external data, producing a real deliverable — that is functionally identical to how a human freelancer works today. Human freelancers read the brief, set up the tools, do the research, and deliver the artifact. So do agents. The difference is the agent can now do it inside a container in just a few seconds. And skills ensure that it follows the same procedure every single time.

Glean is an enterprise search company and it was an early skills customer and they saw accuracy on Salesforce related tasks jump from 73 to 85% with a single well-structured skill. At the same time it got faster because the agent wasn't thinking about what to do and they saw about an 18% decrease in time to first token which matters when every single query counts. The gains come from moving stable procedures out of system prompt and into versioned modular instruction bundles which is frankly again just software engineering applied to AI workflows. We're not reinventing the wheel here. Nothing revolutionary. Everything that is revolutionary comes from second order effects. All we're doing is a classic enterprise deployment except we're doing it with AI. We now have version control, testing, roll back. That part isn't new. The part that's new is that we're doing all of this for autonomous AI agents.

Last but not least, they launched compaction, which is not a particularly flashy feature, but which is super important to support long-running workflows. Any agent running for a while accumulates pages of search results, API responses, calculations, conversation history, and the context window gets dirty. It fills up. The agent starts to forget earlier steps or drift. The agent may crash. Compaction handles all of this server side and automatically summarizes and compresses the context to keep the agent operational across workflows that would otherwise be impossible. It's the kind of feature that makes agents viable for tasks that take longer, like hours instead of just a few minutes. And that kind of sustained multi-step work at scale redefines how easily you can roll out agents across an enterprise environment.

### What Happens When You Combine All the Primitives

So let's step back. What happens when you combine all of the different primitives I have been talking about here? An agent that has a wallet, search capabilities, content access, payment rails, and an execution environment is more than an assistant. It is an economic actor.

Consider what a developer calling himself Chat App demonstrated on X this week. He connected OpenClaw to Kling 2.0, which is a video generation model inside an app called Chatcut. Then he sent the agent an Amazon product link. The agent crawled the Amazon page, extracted product info and photos, identified which assets were suitable for video generation, fed them into Seed Dance, which is an incredible video model, and produced a user-generated content style product video. The kind of content that brands pay creators a thousand bucks to produce. No human touched any step between "paste this link" and "here's your video." I watched it. It looks pretty good.

That is the emergent web. Not an agent doing a task, but agents chaining capabilities together across services to produce outputs that previously required multiple humans and multiple tools. The Amazon page wasn't designed for agents. Kling 2.0 actually wasn't designed to receive input from web crawlers. Chatcut wasn't designed as an orchestration layer, but because each piece exposes its capabilities through APIs and structured data, the agent can stitch them together into a workflow that no individual company planned.

This is the pattern that the infrastructure convergence makes inevitable. When content is available as markdown, search returns structured data, execution happens in containers, and payment flows through tokenized protocols. So the agent doesn't need anybody to build an integration between A and B. It can read both services, understand both, and chain them together on the fly. The emergent web is therefore not a platform that any one person is going to build. It's what happens automatically when the primitives exist and the agent is smart enough to combine them together. And the agents increasingly are.

### The Creator Economy Implications

The implications for the creator economy alone are staggering. The UGC product video would have cost, you know, a thousand bucks and the agent can replicate that workflow from one link, not maybe with human creative judgment, but at a cost that approaches zero and a turnaround time measured in a couple of minutes. If you multiply that by every content type that follows a repeatable pattern, like product descriptions, social media posts, email campaigns, comparison articles, you start to see why the infrastructure companies are building for a scale that isn't there yet. They are seeing a world where this kind of emergent agent behavior is the norm, the default, not just a weird demo from a guy on X.

### Polymarket: Agents Trading to Pay for Compute

Polymarket provides the most provocative case study of where this goes. The prediction market platform processed $12 billion in volume in January 2026 alone. Researchers from IMDIA Networks Institute analyzed 86 million bets and found that algorithmic traders extracted roughly $40 million in arbitrage profits over a 12-month period. The top three wallets placed over 10,000 bets combined. Only half a percent of all Polymarket users earned more than $1,000. The rest were effectively just providing liquidity for bots to extract value.

And here's where it gets even more interesting. Polymarket itself tweeted in early February of this year that quote "autonomous AI agents are now trading on Polymarket in an attempt to subsidize their token costs." Agents are trying to earn money to pay for their own compute. The loop is closing.

Meanwhile, the data on how well agents are doing is mixed but illuminating. OLAS protocol's PolyStrat agents among the most sophisticated autonomous prediction market systems that are being publicly tracked achieve maybe 55 to 65% win rates over time with performance varying really dramatically by domain. Agents tend to be better at predicting things that follow from data rather than things that follow from culture, which is not surprising. It tells you the kind of economic activity that agents are really well suited for versus the kind that maybe humans are well suited for. I'm not sure we'll see an agent doing the Met Gala anytime soon.

The cumulative volume of AI trades on Polymarket is continuing to grow. It's just going to when you have AI agents by the thousand registering for wallets and trying to start getting into currency.

### The TikTok Scam vs the Real Infrastructure Bet

This is where the scam also lives. TikTok right now is flooded with videos of people claiming to turn, I don't know, 50 bucks into 3,000 bucks in a couple of days. These videos get thousands of likes. These videos get thousands of bookmarks. People are clearly hungry for the words AI and make money in the same video. The reality is considerably less glamorous.

The bot that famously turned $313 into $438,000 in a month was running latency arbitrage, exploiting a millisecond gap between when Bitcoin moved on Binance and when Polymarket odds adjusted. That kind of algorithmic trading is not what your Open Claw bot is going to be able to do. That is high-frequency trading which has been known in finance circles for a long time and is just being applied to Polymarket as the market matures. It requires really fancy setups like collocated infrastructure with sub-10 millisecond latency. It requires capital that is a whole lot larger than any TikTok video would suggest.

And if you try and do it with something like an OpenClaw agent, you're going to run into real costs. One developer who actually built and tested an autonomous Polymarket agent reported that Cloudflare blocks API requests from data center IPs and requires custom bypass infrastructure just to place orders. Another one found that running the bot for just a couple of days racked up 200 bucks in API fees alone.

So yes, sophisticated autonomous trading agents can generate returns on Polymarket. No, you cannot replicate this with your Open Claw by feeding it a TikTok tutorial. The infrastructure requirements, the API costs, and the competitive dynamics make this a game for well-capitalized tech operators, not retail experimenters. But the underlying premise, the thing we've been talking about all video, the idea that agents can participate in economic activity and generate revenue, that is not a scam. That is the direction that Coinbase, Stripe, Google, PayPal, Visa, and OpenAI are all aggressively building toward simultaneously with billions of dollars in infrastructure investment. The question isn't whether agents will be able to transact autonomously. The question is whether guardrails will be built fast enough to prevent very predictable disasters.

### Security: Treating Every Agent as a Potential Adversary

I covered OpenClaw's security nightmare in detail in my first video. The one-click remote code execution, malicious skills disguised as crypto tools, Cisco's research team finding data exfiltration in a third party skill. I'm not going to rehash all of that. What I want to focus on instead is the structural problem that those incidents illustrate because it scales with the infrastructure for agent commerce.

Every primitive that makes agents more capable also makes them more dangerous. An agent with a wallet can pay for APIs or get drained by a malicious skill. An agent with shell access can install dependencies or execute arbitrary code injected through a prompt. An agent with search can find information or be redirected to adversarial content designed to manipulate its behavior. And last but not least, an agent with Cloudflare served markdown can read websites or consume poison content at machine speed. It's kind of your choice.

The security community is already responding to the threats that come with these new primitives. And the responses are instructive because they reveal what serious people think the real attack surface is going to look like for agents. IronClaw is a Rust-based re-implementation of OpenClaw by Near.AI co-founder Illia Polosukhin and it sandboxes every single tool that OpenClaw uses into isolated WebAssembly environments. Assumption being that any tool an agent touches is a potential compromise vector. OpenAI's shell tool meanwhile includes org level and request level network allow lists, domain secrets that prevent credential leakage and container isolation. The assumption being that agents will run untrusted code and the environment must contain the blast radius. Coinbase's agentic wallets use enclave isolation for private keys and programmable spending guardrails. The assumption there being that the agent itself cannot be fully trusted with the assets it manages.

Notice the pattern across all of these. Every serious security approach treats the agent as a potential adversary. That is the correct approach. It does not treat the agent like a trusted employee. That is the right mental model for where we're at at this point in 2026. And it's one that most of the TikTok buzz tutorial crowd has not internalized.

### The Mobile Web Analogy and What Comes Next

Look, agents have existed for a while now. APIs have existed for decades. The concept of software transacting with software predates the web itself. What's new is all of these factors converging to make the agentic web. In the span of just a few months, every layer of the stack went from concept to production to infrastructure. Money, content, search, execution, identity is all in production now simultaneously.

The web is starting to fork. There's the human web, the one you're reading right now or listening to a video on right now with fonts and layouts and images and scroll animations. And at the same time, in parallel, on another fork, there's the agent web, a parallel layer of APIs, structured data, markdown content, payment protocols, and execution environments designed for software that will never open a browser. These two webs run on the same physical infrastructure, the same servers, the same CDNs, the same payment rails, but they serve fundamentally different clients with different needs. A human wants a beautiful product page. An agent wants a JSON payload with the price, the availability, and the payment endpoint. A human might want search results they can browse. An agent just wants structured data to act on. A human wants a checkout flow with trust signals. The agent just wants tokenized payment primitives and will be getting on with its day.

The analogy that keeps coming to mind is the early mobile web. In 2007 when the iPhone launched, the web already existed. It worked on phones technically, but it was designed for desktops and the experience was terrible. What followed was a decade long rebuild for the mobile web. Responsive design, mobile first frameworks, app stores, push notifications, GPS-aware services, tap to pay. The underlying infrastructure was the same, but the interface layer forked completely. The companies that recognized the fork early, that built for the new client instead of trying to make the old interface work on the new device, those were the ones that built the dominant platforms of the next era.

We are at the same inflection point today except the new client isn't a smaller screen. It's not a screen at all. It's software that reads, decides, pays, and acts. The interface it needs isn't visual. It's structured. It's programmable. It's transactional. And the companies building that interface right now, they're not the startups that are hoping to get lucky. They're the big boys. They're Coinbase, Stripe, Cloudflare, Google, OpenAI, Visa, PayPal. Companies with the infrastructure, scale, and distribution to make their design decisions into de facto web standards.

The mobile fork created trillion-dollar companies, right? It created Uber, Instagram, WhatsApp, Snap. They would not have existed on the desktop web. Not because the desktop web lacked capabilities, but because it lacked the interface primitives that mobile clients really needed. It lacked real-time location, always on connectivity, camera first interaction, push notifications, tap to pay at physical registers.

The agent fork is going to do the same thing again in the 2020s. The businesses that emerge from it will be the ones that could not have existed on the human web, not because the human web lacks information, but because it lacks the interface primitives that agent clients really need. Structured data, tokenized payments, machine readable content, programmatic search, execution environments.

In my last video on Open Claw, I talked about the 70/30 rule. The idea that people consistently want to maintain maybe roughly 70% human control of agent delegated tasks. That's the demand side. That's the human side of the story, right? This video has really been about the supply side of the story, the agent side of the story. And that side doesn't care about our 70/30 split or what kind of control we want to maintain.

The infrastructure that is being built right now that I have spent this video talking about assumes a 0/100 world. Fully autonomous agents with their own wallets, their own search capabilities, their own execution environments, and their own economic relationships with the services they use. The gap between the infrastructure being built and the trust people are willing to extend to agents is the central tension of the next few years in AI.

Every company in the agent stack is betting that trust will catch up to the capabilities that are being built today. And every security incident that we see, especially with the Open Claw story, things like Claw Havoc, like the 500 message iMessage disaster, production databases being wiped by unsupervised agents, those kinds of stories push the timeline of trust back even though they don't stop people trying agents.

For now, the agent web is really small. Developers running OpenClaw on Mac Minis and VPS instances, AI shopping assistants placing orders through Stripe's ACPs. But small now does not mean small later. Because of how quickly Open Claw is growing, because of how much venture funding is going into agents in 2026, we are likely to see explosive growth in this new branch of the web in 2026.

I don't know if a fully realized agentic web arrives in 3 months, 3 weeks, or 2 years. That's an open question. That it's being built is not a question and I increasingly have no doubt we are headed toward a world where agents are as ubiquitous on the web as people. It is up to us to shape those web standards so they work well for both agents and people. And it's up to us to make sure the primitives that we build like payments, like security, are robust enough that we actually can trust agent operations and agent economics, the way we've learned to trust other humans for commerce over the web. Without that base layer of trust, the future of the agentic web may be stillborn.

And that is the thing I want to leave you with. What is going to build trust in the agentic web? And as much as these companies are investing in primitives, the primitive of trust is something that we are going to have to see realized over time by good faith actors who are building for a future where both humans and agents work on the web together.

---

## COMPASS Integration Notes

### Immediate Relevance
- **Content delivery dual-mode:** COMPASS should be aware that content is increasingly served in both human (HTML) and agent (markdown/structured data) formats. Content optimization strategies need to account for both audiences.
- **Agent commerce protocols:** X402 (Coinbase), Shared Payment Tokens (Stripe), Universal Commerce Protocol (Google) — these are the payment rails COMPASS-optimized campaigns will eventually transact through.
- **llms.txt / llms-full.txt:** New standard for machine-readable sitemaps. COMPASS content strategies should include these alongside traditional SEO sitemaps.
- **Cloudflare AI Index + MCP server:** Sites can make content discoverable to agents directly, bypassing Google. This is a new discovery channel COMPASS should track.

### Strategic Implications
- **Repeatable content patterns are most vulnerable to agent automation:** Product descriptions, social posts, email campaigns, comparison articles. COMPASS positioning should emphasize the orchestration and judgment layer, not the content generation commodity.
- **Fraud detection is being rebuilt:** Stripe retrained Radar from scratch for agent buyers. COMPASS analytics and attribution models will need similar recalibration as agent traffic grows.
- **The trust gap is the opportunity:** Infrastructure assumes 0/100 autonomy, humans want 70/30 control. COMPASS can position in that gap as the human-in-the-loop orchestration layer.
- **Agent-native search changes SEO fundamentally:** Structured data, API-first content, latency optimization matter more than traditional SERP ranking for agent discovery.

### Key Players to Track
| Company | What They Built | Protocol/Product |
|---------|----------------|-----------------|
| Coinbase | Agent crypto wallets | X402, Agentic Wallets |
| Stripe | Agent commerce suite | Shared Payment Tokens, ACS |
| Cloudflare | Agent content delivery | Markdown for Agents, AI Index, MCP |
| Google | Agent commerce standard | Universal Commerce Protocol |
| OpenAI | Agent execution env | Skills, Shell Tools, Compaction |
| Exa.ai | Agent-native search | Neural retrieval, 95% SimpleQA |
| Visa | Agent trust protocol | Trusted Agent Protocol |
| PayPal | Agent checkout | Instant Checkout in ChatGPT |
| IronClaw/Near.AI | Agent security | WASM sandboxing |
